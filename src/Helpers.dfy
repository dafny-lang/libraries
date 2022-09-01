// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module Helpers {
  export 
    provides Comparison

}

module Helpers.Comparison {
  datatype CompResult = LessThan | Equals | GreaterThan 
}