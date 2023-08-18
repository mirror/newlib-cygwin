/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright © 2023 Keith Packard
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#define __STDC_WANT_IEC_60559_BFP_EXT__
#include <math.h>
#include <stdio.h>
#include <float.h>
#include <stdlib.h>
#include <stdbool.h>
#include <fenv.h>

#if FLT_MANT_DIG == 24

static bool
equalf(float x, float y)
{
    if (isnan(x) && isnan(y))
        return true;
    return x == y;
}

static int roundings[] = {
#ifdef FE_TONEAREST
    FE_TONEAREST,
#else
    -1,
#endif
#ifdef FE_UPWARD
    FE_UPWARD,
#endif
#ifdef FE_DOWNWARD
    FE_DOWNWARD,
#endif
#ifdef FE_TOWARDZERO
    FE_TOWARDZERO,
#endif
};

static const char *rounding_names[] = {
#ifdef FE_TONEAREST
    "FE_TONEAREST",
#else
    "default",
#endif
#ifdef FE_UPWARD
    "FE_UPWARD",
#endif
#ifdef FE_DOWNWARD
    "FE_DOWNWARD",
#endif
#ifdef FE_TOWARDZERO
    "FE_TOWARDZERO",
#endif
};

#define NROUND  (sizeof(roundings)/sizeof(roundings[0]))

#ifdef PICOLIBC_DOUBLE_NOEXCEPT
/*
 * Assume that a lack of exceptions for doubles also means a lack of
 * support for non-default rounding modes for doubles.
 */
#define SKIP_ROUNDINGS_FLOAT
#endif

#ifdef SKIP_ROUNDINGS_FLOAT
#define NROUND_FLOAT    1
#else
#define NROUND_FLOAT NROUND
#endif

#if defined(__PICOLIBC__) && !defined(TINY_STDIO)
static
int strfromf(char *str, size_t n, const char *format, float f)
{
    return snprintf(str, n, format, (double) f);
}
#endif

#define nanf __builtin_nanf("")
#define inff INFINITY
#define nan __builtin_nan("")
#define inf ((double) INFINITY)
#define nanl __builtin_nanl("")
#define infl ((long double) INFINITY)

struct fmaf_vec {
    float       x, y, z;
    float       r[4];
};

struct fma_vec {
    double      x, y, z;
    double      r[4];
};

#ifdef _TEST_LONG_DOUBLE
struct fmal_vec {
    long double      x, y, z;
    long double      r[4];
};
#endif

#include "fma_vec.h"

#define NUM_FMAF_VEC (sizeof(fmaf_vec)/sizeof(fmaf_vec[0]))
#define NUM_FMA_VEC (sizeof(fma_vec)/sizeof(fma_vec[0]))
#define NUM_FMAL_VEC (sizeof(fmal_vec)/sizeof(fmal_vec[0]))

static int
test_fmaf(void)
{
    char        xs[20], ys[20], zs[20], rs[20], ss[20];
    int ret = 0;
    unsigned int ro;
    int defround = fegetround();
    unsigned int t;

    printf("float\n");
    for (t = 0; t < NUM_FMAF_VEC; t++) {
        for (ro = 0; ro < NROUND_FLOAT; ro++) {
            if (roundings[ro] == -1)
                fesetround(defround);
            else
                fesetround(roundings[ro]);
            float x = fmaf_vec[t].x;
            float y = fmaf_vec[t].y;
            float z = fmaf_vec[t].z;
            float r = fmaf(x, y, z);
            float s = fmaf_vec[t].r[ro];
            if (!equalf(r, s)) {
                strfromf(xs, sizeof(xs), "%a", x);
                strfromf(ys, sizeof(xs), "%a", y);
                strfromf(zs, sizeof(xs), "%a", z);
                strfromf(rs, sizeof(xs), "%a", r);
                strfromf(ss, sizeof(xs), "%a", s);
                printf("%u: round %s %s %s %s -> got %s want %s\n",
                       t, rounding_names[ro],
                       xs, ys, zs, rs, ss);
                ret = 1;
            }
        }
    }
    fesetround(defround);
    return ret;
}
#else
#define test_fmaf() 0
#endif

#if DBL_MANT_DIG == 53

#ifdef PICOLIBC_DOUBLE_NOEXCEPT
/*
 * Assume that a lack of exceptions for doubles also means a lack of
 * support for non-default rounding modes for doubles.
 */
#define SKIP_ROUNDINGS_DOUBLE
#endif

#ifdef SKIP_ROUNDINGS_DOUBLE
#define NROUND_DOUBLE    1
#else
#define NROUND_DOUBLE NROUND
#endif

static bool
equal(double x, double y)
{
    if (isnan(x) && isnan(y))
        return true;
    return x == y;
}

static int
test_fma(void)
{
    char        xs[24], ys[24], zs[24], rs[24], ss[24];
    int ret = 0;
    unsigned int ro;
    int defround = fegetround();
    unsigned int t;

    printf("double\n");
    for (t = 0; t < NUM_FMA_VEC; t++) {
        for (ro = 0; ro < NROUND_DOUBLE; ro++) {
            if (roundings[ro] == -1)
                fesetround(defround);
            else
                fesetround(roundings[ro]);
            double x = fma_vec[t].x;
            double y = fma_vec[t].y;
            double z = fma_vec[t].z;
            double r = fma(x, y, z);
            double s = fma_vec[t].r[ro];
            if (!equal(r, s)) {
                strfromd(xs, sizeof(xs), "%a", x);
                strfromd(ys, sizeof(xs), "%a", y);
                strfromd(zs, sizeof(xs), "%a", z);
                strfromd(rs, sizeof(xs), "%a", r);
                strfromd(ss, sizeof(xs), "%a", s);
                printf("%u: round %s %s %s %s -> got %s want %s\n",
                       t, rounding_names[ro],
                       xs, ys, zs, rs, ss);
                ret = 1;
            }
        }
    }
    fesetround(defround);
    return ret;
}
#else
#define test_fma() 0
#endif

#if LDBL_MANT_DIG == 64 || LDBL_MANT_DIG == 113

#ifdef PICOLIBC_LONG_DOUBLE_NOEXCEPT
/*
 * Assume that a lack of exceptions for doubles also means a lack of
 * support for non-default rounding modes for doubles.
 */
#define SKIP_ROUNDINGS_LONG_DOUBLE
#endif

#ifdef SKIP_ROUNDINGS_LONG_DOUBLE
#define NROUND_LONG_DOUBLE    1
#else
#define NROUND_LONG_DOUBLE NROUND
#endif

static bool
equall(long double x, long double y)
{
    if (isnan(x) && isnan(y))
        return true;
    return x == y;
}

static int
test_fmal(void)
{
    int ret = 0;
    unsigned int ro;
    int defround = fegetround();
    unsigned int t;

    printf("long double\n");
    for (t = 0; t < NUM_FMAL_VEC; t++) {
        for (ro = 0; ro < NROUND_LONG_DOUBLE; ro++) {
            if (roundings[ro] == -1)
                fesetround(defround);
            else
                fesetround(roundings[ro]);
            long double x = fmal_vec[t].x;
            long double y = fmal_vec[t].y;
            long double z = fmal_vec[t].z;
            long double r = fmal(x, y, z);
            long double s = fmal_vec[t].r[ro];
            if (!equall(r, s)) {
                printf("%u: round %s %La * %La + %La -> got %La want %La\n",
                       t, rounding_names[ro],
                       x, y, z, r, s);
                ret = 1;
            }
        }
    }
    fesetround(defround);
    return ret;
}
#else
#define test_fmal() 0
#endif

int
main(void)
{
#ifdef __arc__
    volatile float x = 0x1.000002p-2f;
    volatile float y = 0x1.000002p-126f;
    volatile float z = 0x0.400002p-126f;
    if (x * y != z) {
        printf("ARC soft float bug, skipping FMA tests\n");
        return 77;
    }
#endif
    return test_fmaf() || test_fma() || test_fmal();
}
