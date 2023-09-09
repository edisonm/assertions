#ifndef __foreign_test_H
#define __foreign_test_H

typedef int negative_t;

/*
#define FI_get_positive_t(__root, __term, __value) {	\
    PL_get_integer(__term, __value) &&			\
      is_positive_t(*__value);				\
  }

#define FI_unify_positive_t(__term, __value) {		\
    PL_unify_integer(__term, *__value) &&		\
      is_positive_t(*__value);				\
  }
*/

#define FI_get_negative_t(__root, __term, __value)  PL_get_integer(__term, __value)
#define FI_unify_negative_t(__term, __value)        PL_unify_integer(__term, __value)

#endif
