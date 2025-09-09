/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

package DafnyLibraries;

import dafny.*;
import java.math.*;

public class Random {
    public static boolean nextBool()
    {
        return Math.random() < 0.5;
    }
    public static BigInteger nextInt(BigInteger Bound)
    {
        long bound = Bound.longValue();
        long bnd = bound > 0 ? bound : Long.MAX_VALUE;
        return BigInteger.valueOf((long) Math.floor(Math.random() * bnd));
    }
    public static BigRational nextReal()
    {
        long num = (long) Math.floor(Math.random() * Long.MAX_VALUE);
        long den = Long.MAX_VALUE;
        return new BigRational(BigInteger.valueOf(num), BigInteger.valueOf(den));
    }
}
