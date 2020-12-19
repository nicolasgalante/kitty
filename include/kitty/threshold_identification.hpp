/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification
  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "operations.hpp"
#include "isop.hpp"
#include "cube.hpp"
#include "bit_operations.hpp"
#include "operators.hpp"
#include "properties.hpp"
#include "implicant.hpp"

namespace kitty
{

/*! \brief Threshold logic function identification
  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as
  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T
  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].
  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of tt if it is a TF.
             The linear form has tt.num_vars() weight values and the threshold value
             in the end.
  \return true if tt is a TF; false if tt is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  auto tt_changed = tt;
  //bool binate = false;


  /* TODO */
  /* if tt is non-TF: */
  /* chekc for unateness */

  int var_num = tt.num_vars(); /*I am calling var_num to differentiate it visually from num_vars*/

  std::vector<bool> invert_var(var_num, false);

  for (auto i = 0; i < var_num; i++) {

    /*check_if_unate(tt_changed, invert_var, i, binate);
    if (binate) {
      return false;
    }*/
    auto const tt_cof_neg = cofactor0( tt_changed, i);
    auto const tt_cof_pos = cofactor1( tt_changed, i);

    if ( implies(tt_cof_neg, tt_cof_pos) ) {
      tt_changed = tt_changed;
    }


    else if ( implies(tt_cof_pos, tt_cof_neg) ) {
      invert_var[i] = true;
      tt_changed = flip(tt_changed, i) ;
    }

    else return false;
  }

  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  lprec *lp;
  int Ncol, *colno = NULL, j, ret = 0;
  REAL *row = NULL;

  /* We will build the model row by row
     So we start with creating a model with 0 rows and 2 columns */
  Ncol = var_num + 1; /* there are two variables in the model */
  lp = make_lp(0, Ncol);
  if(lp == NULL)
    return false; /* couldn't construct a new model... */

  //if(ret == 0) {
    /* let us name our variables. Not required, but can be useful for debugging */
    //set_col_name(lp, 1, "x");
    //set_col_name(lp, 2, "y");

    /* create space large enough for one row */
    colno = (int *) malloc(Ncol * sizeof(*colno));
    row = (REAL *) malloc(Ncol * sizeof(*row));
    if((colno == NULL) || (row == NULL))
      return false;
      //ret = 2;
  //}


  auto onset_impl = get_prime_implicants_morreale( tt_changed );
  auto offset_impl = get_prime_implicants_morreale(unary_not(tt_changed));

  set_add_rowmode(lp, TRUE);

  //if(ret == 0) {
  /* makes building the model faster if it is done rows by row */

  /* construct first row (120 x + 210 y <= 15000) */
  for (auto p : onset_impl) {
    j = 0;

    for (int i = 0; i < var_num; i++) {
      if ( p.get_bit(i) ) {
        colno[j] = i + 1;
        row[j++] = 1;
      }
    }
    row[j] = -1;
    colno[j++] = Ncol;

    add_constraintex(lp, j, row, colno, GE, 0) ;    /* add the row to lpsolve */
      //return false;
      //ret = 3;
  }

  //}

  //if(ret == 0) {
    /* construct second row (110 x + 30 y <= 4000) */
  for (auto pn : offset_impl) {
    j = 0;

    for (int i = 0; i < var_num; i++) {
      if ( !pn.get_mask(i) ) {
        colno[j] = i + 1;
        row[j++] = 1;
      }
    }
    row[j] = -1;
    colno[j++] = Ncol;

    add_constraintex(lp, j, row, colno, LE, -1);    /* add the row to lpsolve */
    //ret = 3;
    //return false;
  }
  //}
  set_add_rowmode(lp, FALSE); /* rowmode should be turned off again when done building the model */

  //if(ret == 0) {

    /* set the objective function */
    //j = 0;

  for (int i = 0; i < Ncol; i++) {
    colno[i] = i + 1;
    row[i] = 1;

  }

    /* set the objective in lpsolve */
  set_obj_fnex( lp, Ncol, row, colno );
  //}
  //if(ret == 0) {
    /* set the object direction to minimize */
  set_minim( lp );
  /* just out of curioucity, now show the model in lp format on screen */
  /* this only works if this is a console application. If not, use write_lp and a filename */
  //write_LP(lp, stdout);
  /* write_lp(lp, "model.lp"); */

  /* I only want to see important messages on screen while solving */

  set_verbose( lp, IMPORTANT );

    /* Now let lpsolve calculate a solution */

  ret = solve( lp );
  //if it is not a TF return out
  if ( ret != OPTIMAL )
    return false;

    //if(ret == 0) {
      /* a solution is calculated, now lets get some results */

      /* objective value */
      //printf("Objective value: %f\n", get_objective(lp)); we don't wnat to print in this program

      /* variable values */
      get_variables(lp, row);
    //  for(j = 0; j < Ncol; j++)
    //    printf("%s: %f\n", get_col_name(lp, j + 1), row[j]);

    /*  we need to take care of the linear form*/

  int thresh = row[var_num];

  for ( int i = 0; i < var_num; i++ ) {

    if ( invert_var[i] ) {
     linear_form.push_back( (-1)*row[i] );
     thresh = thresh + linear_form[i];
    }

    else {
     linear_form.push_back( row[i] );

    }

  }

  linear_form.push_back( thresh );

  /* we are done now */

  if ( plf )
  {
    *plf = linear_form;
  }



/* free allocated memory */
if(row != NULL)
  free(row);

if(colno != NULL)
  free(colno);

if(lp != NULL) {
  /* clean up such that all used memory by lpsolve is freed */
  delete_lp(lp);
}




  return true;
}


} /* namespace kitty */
