/*
 * Copyright (c) 1996 by Internet Software Consortium.
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND INTERNET SOFTWARE CONSORTIUM DISCLAIMS
 * ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL INTERNET SOFTWARE
 * CONSORTIUM BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL
 * DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
 * PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS
 * ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS
 * SOFTWARE.
 */

/* Author: Paul Vixie (ISC), June 1996 */
/* Copied from Linux, modified for Phoenix-RTOS. */

#include <arpa/inet.h>
#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <netinet/in.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>

static int inet_net_pton_ipv4(const char *src, u_char *dst, size_t size)
{
	static const char xdigits[] = "0123456789abcdef";
	static const char digits[] = "0123456789";
	int n, ch, tmp, dirty, bits;
	const u_char *odst = dst;
	ch = *src++;

	if (ch == '0' && (src[0] == 'x' || src[0] == 'X') && isascii(src[1]) && isxdigit(src[1])) {
		/* Hexadecimal: Eat nybble string. */
		if (size <= 0)
			goto emsgsize;

		*dst = 0, dirty = 0;
		src++;	/* skip x or X. */

		while ((ch = *src++) != '\0' &&
		        isascii(ch) && isxdigit(ch)) {
			if (isupper(ch))
				ch = tolower(ch);

			n = strchr(xdigits, ch) - xdigits;
			assert(n >= 0 && n <= 15);
			*dst |= n;

			if (!dirty++)
				*dst <<= 4;

			else
				if (size-- > 0)
					*++dst = 0, dirty = 0;

				else
					goto emsgsize;
		}

		if (dirty)
			size--;
	}
	else {
		if (isascii(ch) && isdigit(ch)) {
			/* Decimal: eat dotted digit string. */
			for (;;) {
				tmp = 0;

				do {
					n = strchr(digits, ch) - digits;
					assert(n >= 0 && n <= 9);
					tmp *= 10;
					tmp += n;

					if (tmp > 255)
						goto enoent;
				}
				while ((ch = *src++) != '\0' && isascii(ch) && isdigit(ch));

				if (size-- <= 0)
					goto emsgsize;

				*dst++ = (u_char) tmp;

				if (ch == '\0' || ch == '/')
					break;

				if (ch != '.')
					goto enoent;

				ch = *src++;

				if (!isascii(ch) || !isdigit(ch))
					goto enoent;
			}
		}
		else
			goto enoent;
	}

	bits = -1;

	if (ch == '/' && isascii(src[0]) && isdigit(src[0]) && dst > odst) {
		/* CIDR width specifier.  Nothing can follow it. */
		ch = *src++;	/* Skip over the /. */
		bits = 0;

		do {
			n = strchr(digits, ch) - digits;
			assert(n >= 0 && n <= 9);
			bits *= 10;
			bits += n;
		}
		while ((ch = *src++) != '\0' && isascii(ch) && isdigit(ch));

		if (ch != '\0')
			goto enoent;

		if (bits > 32)
			goto emsgsize;
	}

	/* Firey death and destruction unless we prefetched EOS. */
	if (ch != '\0')
		goto enoent;

	/* If nothing was written to the destination, we found no address. */
	if (dst == odst)
		goto enoent;

	/* If no CIDR spec was given, infer width from net class. */
	if (bits == -1) {
		if (*odst >= 240)	/* Class E */
			bits = 32;

		else
			if (*odst >= 224)	/* Class D */
				bits = 4;

			else
				if (*odst >= 192)	/* Class C */
					bits = 24;

				else
					if (*odst >= 128)	/* Class B */
						bits = 16;

					else			/* Class A */
						bits = 8;

		/* If imputed mask is narrower than specified octets, widen. */
		if (bits >= 8 && bits < ((dst - odst) * 8))
			bits = (dst - odst) * 8;
	}

	/* Extend network to cover the actual mask. */
	while (bits > ((dst - odst) * 8)) {
		if (size-- <= 0)
			goto emsgsize;

		*dst++ = '\0';
	}

	return (bits);
enoent:
	errno = ENOENT;
	return -1;

emsgsize:
	errno = EMSGSIZE;
	return -1;
}

int inet_net_pton(int af, const char *pres, void *netp, size_t nsize)
{
	switch (af) {
	case AF_INET:
		return inet_net_pton_ipv4(pres, netp, nsize);

	default:
		errno = EAFNOSUPPORT;
		return -1;
	}
}
