/* winf.cc

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */

#include "winsup.h"
#include <stdlib.h>
#include "cygerrno.h"
#include "security.h"
#include "path.h"
#include "fhandler.h"
#include "dtable.h"
#include "cygheap.h"
#include "tls_pbuf.h"
#include "winf.h"
#include "sys/cygwin.h"
#include "glob.h"

void
linebuf::finish (bool trunc_for_cygwin)
{
  if (!ix)
    add ("", 1);
  else
    {
      if (ix-- > MAXCYGWINCMDLEN && trunc_for_cygwin)
	ix = MAXCYGWINCMDLEN - 1;
      buf[ix] = '\0';
    }
}

void
linebuf::add (const char *what, int len)
{
  size_t newix = ix + len;
  if (newix >= alloced || !buf)
    {
      alloced += LINE_BUF_CHUNK + newix;
      buf = (char *) realloc (buf, alloced + 1);
    }
  memcpy (buf + ix, what, len);
  ix = newix;
  buf[ix] = '\0';
}

void
linebuf::prepend (const char *what, int len)
{
  int buflen;
  size_t newix;
  if ((newix = ix + len) >= alloced)
    {
      alloced += LINE_BUF_CHUNK + newix;
      buf = (char *) realloc (buf, alloced + 1);
      buf[ix] = '\0';
    }
  if ((buflen = strlen (buf)))
      memmove (buf + len, buf, buflen + 1);
  else
      buf[newix] = '\0';
  memcpy (buf, what, len);
  ix = newix;
}

bool
linebuf::fromargv (av& newargv, const char *real_path, bool trunc_for_cygwin, bool forcequote)
{
  bool success = true;
  for (int i = 0; i < newargv.argc; i++)
    {
      char *p = NULL;
      const char *a;

      a = i ? newargv[i] : (char *) real_path;
      int len = strlen (a);
      if (len != 0 && !forcequote && !strpbrk (a, " \t\n\r\""))
	add (a, len);
      else
	{
	  add ("\"", 1);
	  /* Handle embedded special characters " and \.
	     A " is always preceded by a \.
	     A \ is not special unless it precedes a ".  If it does,
	     then all preceding \'s must be doubled to avoid having
	     the Windows command line parser interpret the \ as quoting
	     the ".  This rule applies to a string of \'s before the end
	     of the string, since cygwin/windows uses a " to delimit the
	     argument. */
	  for (; (p = strpbrk (a, "\"\\")); a = ++p)
	    {
	      add (a, p - a);
	      /* Find length of string of backslashes */
	      int n = strspn (p, "\\");
	      if (!n)
		add ("\\\"", 2);	/* No backslashes, so it must be a ".
					       The " has to be protected with a backslash. */
	      else
		{
		  add (p, n);	/* Add the run of backslashes */
		  /* Need to double up all of the preceding
		     backslashes if they precede a quote or EOS. */
		  if (!p[n] || p[n] == '"')
		    add (p, n);
		  p += n - 1;		/* Point to last backslash */
		}
	    }
	  if (*a)
	    add (a);
	  add ("\"", 1);
	}
      add (" ", 1);
    }

  finish (trunc_for_cygwin);

  if (ix >= MAXWINCMDLEN)
    {
      debug_printf ("command line too long (>32K), return E2BIG");
      set_errno (E2BIG);
      success = false;
    }

  return success;
}

int
av::unshift (const char *what)
{
  char **av;
  av = (char **) crealloc (argv, (argc + 2) * sizeof (char *));
  if (!av)
    return 0;

  argv = av;
  memmove (argv + 1, argv, (argc + 1) * sizeof (char *));
  *argv = cstrdup1 (what);
  calloced++;
  argc++;
  return 1;
}

/*
 * Read a file into a newly-allocated buffer.
 */
static char* __reg1
read_file (const char *name)
{
  HANDLE f;
  DWORD size;
  tmp_pathbuf tp;

  PWCHAR wname = tp.w_get ();
  sys_mbstowcs (wname, NT_MAX_PATH, name);	/* FIXME: Do we need \\?\ ? */
  f = CreateFileW (wname,
		   GENERIC_READ,		/* open for reading	*/
		   FILE_SHARE_VALID_FLAGS,      /* share for reading	*/
		   &sec_none_nih,		/* default security	*/
		   OPEN_EXISTING,		/* existing file only	*/
		   FILE_ATTRIBUTE_NORMAL,	/* normal file		*/
		   NULL);			/* no attr. template	*/

  if (f == INVALID_HANDLE_VALUE)
    {
      debug_printf ("couldn't open file '%s', %E", name);
      return NULL;
    }

  /* This only supports files up to about 4 billion bytes in
     size.  I am making the bold assumption that this is big
     enough for this feature */
  size = GetFileSize (f, NULL);
  if (size == 0xFFFFFFFF)
    {
      debug_printf ("couldn't get file size for '%s', %E", name);
      CloseHandle (f);
      return NULL;
    }

  char *string = (char *) malloc (size + 1);
  if (!string)
    {
      CloseHandle (f);
      return NULL;
    }

  /* malloc passed as it should */
  DWORD rf_read;
  BOOL rf_result;
  rf_result = ReadFile (f, string, size, &rf_read, NULL);
  if (!rf_result || (rf_read != size))
    {
      CloseHandle (f);
      return NULL;
    }
  string[size] = '\0';
  return string;
}

static inline int
isquote (char c)
{
  char ch = c;
  return ch == '"' || ch == '\'';
}

static inline int
issep (char c)
{
  return c && (strchr (" \t\n\r", c) != NULL);
}

/* MSVCRT-like argument parsing.
 * Parse a word in-place, consuming characters and marking where quoting state is changed. */
static bool __reg3
next_arg (char *&cmd, char *&arg, size_t* quotepos, size_t &quotesize)
{
  bool inquote = false;
  size_t nbs = 0;
  char quote = '\0';
  size_t nquotes = 0;

  while (*cmd && issep (*cmd))
    cmd++;

  arg = cmd;
  char *out = arg;

  for (;*cmd && (inquote || !issep (*cmd)); cmd++)
    {
      if (*cmd == '\\')
	{
	  nbs += 1;
	  continue;
	}

      // For anything else, sort out backslashes first.
      // All backslashes are literal, except these before a quote.
      // Single-quote is our addition.  Would love to remove it.
      bool atquote = inquote ? *cmd == quote : isquote (*cmd);
      size_t n = atquote ? nbs / 2 : nbs;
      memset (out, '\\', n);
      out += n;

      if (nbs % 2 == 0 && atquote)
	{
	  /* The infamous "" special case: emit literal '"', no change.
	   *
	   * Makes quotepos tracking easier, so applies to single quote too:
	   * without this handling, an out pos can contain many state changes,
	   * so a check must be done before appending. */
	  if (inquote && *cmd == quote && cmd[1] == quote)
	    *out++ = *cmd++;
	  else
	    {
	      if (!inquote)
		quote = *cmd;
	      if (nquotes > quotesize - 1)
		quotepos = realloc_type(quotepos, quotesize *= 2, size_t);
	      quotepos[nquotes++] = out - arg + inquote;
	      inquote = !inquote;
	    }
	}
      else
	{
	  *out++ = *cmd;
	}

      nbs = 0;
    }

  if (*cmd)
    cmd++;

  *out = '\0';
  quotepos[nquotes++] = SIZE_MAX;
  return arg != cmd;
}


/* Either X:[...] or \\server\[...] */
#define is_dos_path(s) (isdrive(s) \
			|| ((s)[0] == '\\' \
			    && (s)[1] == '\\' \
			    && isalpha ((s)[2]) \
			    && strchr ((s) + 3, '\\')))


/* Perform a glob on word if it contains wildcard characters.
   Also quote every character between quotes to force glob to
   treat the characters literally.

   Call glob(3) on the word, and fill argv accordingly.
   If the input looks like a DOS path, double up backslashes.
 */
static int __reg3
globify (const char *word, size_t *quotepos, size_t quotesize, char **&argv, int &argc, int &argvlen)
{
  if (*word != '~' && strpbrk (word, "?*[\"\'(){}") == NULL)
    return 0;

  /* We'll need more space if there are quoting characters in
     word.  If that is the case, doubling the size of the
     string should provide more than enough space. */
  size_t n = quotepos[0] == SIZE_MAX ? 0 : strlen (word);
  char *p;
  const char *s;
  int dos_spec = is_dos_path (word);
  char pattern[strlen (word) + ((dos_spec + 1) * n) + 1];
  bool inquote = false;
  size_t nquotes = 0;

  /* Fill pattern with characters from word, quoting any
     characters found within quotes. */
  for (p = pattern, s = word; *s != '\000'; s++, p++)
    {
      if (nquotes < quotesize)
	{
	  if (quotepos[nquotes] == SIZE_MAX)
	    quotesize = nquotes;
	  else if (quotepos[nquotes] == size_t (s - word))
	    {
	      inquote = !inquote;
	      nquotes++;
	    }
	}
      if (!inquote)
	{
	  if (dos_spec && *s == '\\')
	    *p++ = '\\';
	  *p = *s;
	}
      else
	{
	  *p++ = '\\';
	  int cnt = isascii (*s) ? 1 : mbtowc (NULL, s, MB_CUR_MAX);
	  if (cnt <= 1)
	    *p = *s;
	  else
	    {
	      memcpy (p, s, cnt);
	      p += cnt - 1;
	      s += cnt - 1;
	    }
	}
    }
  *p = '\0';

  glob_t gl;
  gl.gl_offs = 0;

  /* Attempt to match the argument.  Bail if no match. */
  if (glob (pattern, GLOB_TILDE | GLOB_BRACE, NULL, &gl) || !gl.gl_pathc)
    return 0;

  /* Allocate enough space in argv for the matched filenames. */
  n = argc;
  if ((argc += gl.gl_pathc) > argvlen)
    {
      argvlen = argc + 10;
      char **old_argv = argv;
      argv = (char **) realloc (argv, (1 + argvlen) * sizeof (argv[0]));
      if (!argv)
	{
	  free (gl.gl_pathv);
	  argv = old_argv;
	  return -ENOMEM;
	}
    }

  /* Copy the matched filenames to argv. */
  char **gv = gl.gl_pathv;
  char **av = argv + n;
  while (*gv)
    {
      debug_printf ("argv[%zu] = '%s'", n++, *gv);
      *av++ = *gv++;
    }

  /* Clean up after glob. */
  free (gl.gl_pathv);
  return 1;
}

/* Build argv, argc from string passed from Windows. */
extern "C" int
cygwin_cmdline_parse (char *cmd, char ***pargv, char **allocs, int doglob, int maxfile)
{
  int argvlen = 0;
  int nesting = 0;	      // nesting depth for @file (file_stack index)
  int inserts = 0;	      // total @file encountered (allocs index)

  // Would be a bad idea to use alloca due to unbounded file size.
  size_t quotesize = 32;
  size_t *quotepos = malloc_type (quotesize, size_t);

  int argc = 0;
  int error = 0;
  char **argv = NULL;
  char *word;

  bool bail_on_file = maxfile > 0;
  maxfile = bail_on_file ? maxfile : -maxfile;
  char *file_stack[maxfile];
  bool has_next;

  /* Scan command line until there is nothing left. */
  while ((has_next = next_arg (cmd, word, quotepos, quotesize)) || nesting)
    {
      /* Catch when "nothing" is reached but we can pop the stack. */
      if (! has_next)
	{
	  cmd = file_stack[--nesting];
	  continue;
	}

      /* Possibly look for @file construction assuming that this isn't
	 the very first argument and the @ wasn't quoted */
      if (argc && quotepos[0] > 0 && *word == '@')
	{
	  bool do_include = inserts < maxfile;
	  char *fbuf;
	  if (!do_include && bail_on_file)
	    {
	      error = -EMLINK;
	      goto exit;
	    }
	  if (do_include && (fbuf = read_file (word + 1)))
	    {
	      file_stack[nesting++] = cmd;
	      if (allocs != NULL)
		allocs[inserts] = fbuf;

	      inserts += 1;
	      cmd = fbuf;
	      continue;
	    }
	}

      /* See if we need to allocate more space for argv */
      if (argc >= argvlen)
	{
	  argvlen = argc + 10;
	  char **old_argv = argv;
	  argv = (char **) realloc (old_argv, (1 + argvlen) * sizeof (argv[0]));
	  if (!argv)
	    {
	      argv = old_argv;
	      error = -ENOMEM;
	      goto exit;
	    }
	}

      /* Add word to argv file after (optional) wildcard expansion. */
      if (!doglob || !argc || (error = globify (word, quotepos, quotesize, argv, argc, argvlen)) > 0)
	{
	  debug_printf ("argv[%d] = '%s'", argc, word);
	  argv[argc++] = word;
	}
      else if (error)
	{
	  goto exit;
	}
    }

exit:
  if (argv)
    argv[argc] = NULL;
  if (allocs != NULL)
    allocs[inserts] = NULL;

  free (quotepos);
  debug_printf ("argc %d", argc);

  *pargv = argv;
  return error ? error : argc;
}
