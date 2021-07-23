// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* Every lemma comes in 2 forms: 'lemma_property' and 'lemma_property_auto'. The former takes arguments and may 
be more stable and less reliant on Z3 heuristics. The latter includes automation and its use requires less effort */

include "Internals/GeneralInternals.dfy"
include "Internals/MulInternals.dfy"
include "Power.dfy"

module Power2 {
  import opened GeneralInternals
  import opened MulInternals
  import opened Power

  function method {:opaque} power2(e: nat): nat
    ensures power2(e) > 0
  {
    reveal_power();
    lemma_power_positive(2, e);
    power(2, e)
  }

  /* power2() is equivalent to power() with base 2. */
  lemma lemma_power2_is_power_2(e: nat)
    ensures power2(e) == power(2, e)
  {
    reveal_power();
    reveal_power2();
  
    if e != 0 {
      lemma_power2_is_power_2(e - 1);
    }
  }

  lemma lemma_power2_is_power_2_auto()
    ensures forall e: nat {:trigger power2(e)} :: power2(e) == power(2, e)
  {
    reveal_power();
    reveal_power2();
    
    forall e: nat {:trigger power2(e)}
      ensures power2(e) == power(2, e)
    {
      lemma_power2_is_power_2(e);
    }
  }

  /* (2^e - 1) / 2 = 2^(e - 1) - 1 */
  // keep
  lemma lemma_power2_mask_div_2(e: nat)
    requires 0 < e
    ensures (power2(e) - 1) / 2 == power2(e - 1) - 1
  {
    lemma_power_auto();
    var f := e => 0 < e ==> (power2(e) - 1) / 2 == power2(e - 1) - 1;
    assert forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger is_le(i, 0)} :: is_le(i, 0) && f(i) ==> f(i - 1);
    lemma_mul_induction_auto(e, f);
  }

  lemma lemma_power2_mask_div_2_auto()
    ensures forall e: nat {:trigger power2(e)} :: 0 < e ==>
      (power2(e) - 1) / 2 == power2(e - 1) - 1
  {
    reveal_power2();
    forall e: nat {:trigger power2(e)} | 0 < e
      ensures (power2(e) - 1) / 2 == power2(e - 1) - 1
    {
      lemma_power2_mask_div_2(e);
    }
  }

  lemma lemma_power2_2to64()
    ensures power2(0) == 0x1
    ensures power2(1) == 0x2
    ensures power2(2) == 0x4
    ensures power2(3) == 0x8
    ensures power2(4) == 0x10
    ensures power2(5) == 0x20
    ensures power2(6) == 0x40
    ensures power2(7) == 0x80
    ensures power2(8) == 0x100
    ensures power2(9) == 0x200
    ensures power2(10) == 0x400
    ensures power2(11) == 0x800
    ensures power2(12) == 0x1000
    ensures power2(13) == 0x2000
    ensures power2(14) == 0x4000
    ensures power2(15) == 0x8000
    ensures power2(16) == 0x10000
    ensures power2(17) == 0x20000
    ensures power2(18) == 0x40000
    ensures power2(19) == 0x80000
    ensures power2(20) == 0x100000
    ensures power2(21) == 0x200000
    ensures power2(22) == 0x400000
    ensures power2(23) == 0x800000
    ensures power2(24) == 0x1000000
    ensures power2(25) == 0x2000000
    ensures power2(26) == 0x4000000
    ensures power2(27) == 0x8000000
    ensures power2(28) == 0x10000000
    ensures power2(29) == 0x20000000
    ensures power2(30) == 0x40000000
    ensures power2(31) == 0x80000000
    ensures power2(32) == 0x100000000
    ensures power2(64) == 0x10000000000000000
  {
    reveal_power2();
  }

} 
