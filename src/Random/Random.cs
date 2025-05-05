/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

namespace DafnyLibraries
{
    using Dafny;
    using System;
    using System.Numerics;
    public class Random
    {
        private static System.Random rnd = new System.Random();
        public static bool nextBool()
        {
            return rnd.Next(2) == 0;
        }
        public static BigInteger nextInt(BigInteger Bound)
        {
            Int64 bound = (Int64) Bound;
            Int64 bnd = bound > 0 ? bound : Int64.MaxValue;
            return new BigInteger(rnd.NextInt64(bound));
        }
        public static BigRational nextReal()
        {
            Int64 num = rnd.NextInt64();
            Int64 den = Int64.MaxValue;
            return new BigRational(new BigInteger(num), new BigInteger(den));
        }
    }
}
