/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# G-rings and regular ring maps

Source: Stacks Project, Algebra, Definition 0382 and Lemma 0381; More on Algebra,
Definitions 07BZ and 07GH (blueprint: theorem-finite-etale-covers-proper-henselian--2).

## Main definitions

* `Algebra.IsGeometricallyRegular`: geometric regularity over a field.
* `RingHom.IsRegular`: flat maps with geometrically regular fibres.
* `IsGRing`: Noetherian rings with regular local completion maps.
-/

@[expose] public section

universe u v

namespace Algebra

/-- A Noetherian algebra over a field is geometrically regular when base change to every finite
purely inseparable field extension is a regular ring. Source: Stacks, Algebra, Definition 0382
and Lemma 0381, condition (2) (blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
def IsGeometricallyRegular (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] : Prop :=
  IsNoetherianRing A ∧
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Module.Finite k k']
      [IsPurelyInseparable k k'], IsRegularRing (TensorProduct k k' A)

end Algebra

namespace RingHom

/-- A regular ring map is flat and has Noetherian, geometrically regular fibres at every prime.
The Noetherian condition is part of `Algebra.IsGeometricallyRegular`. Source: Stacks,
More on Algebra, Definition 07BZ (blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
def IsRegular {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  f.Flat ∧ ∀ (p : Ideal R) [p.IsPrime],
    Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S)

end RingHom

/-- A G-ring is a Noetherian ring whose map from every prime localization to its adic
completion at the maximal ideal is regular. Source: Stacks, More on Algebra,
Definition 07GH (blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ ∀ (p : Ideal R) [p.IsPrime],
    RingHom.IsRegular
      (algebraMap (Localization.AtPrime p)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)))
