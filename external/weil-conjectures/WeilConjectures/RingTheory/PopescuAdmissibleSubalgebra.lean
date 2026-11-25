/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Admissible subalgebras in the Popescu construction

Source: Stacks Project, proof of Tag 07FH
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

universe uA vA

namespace Subalgebra

/-- An admissible subalgebra is Artinian local, essentially of finite type over the base,
flatly included in the ambient ring, with its maximal ideal generating the specified ambient
ideal. Source: Stacks Project, proof of Tag 07FH
(blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
def IsPopescuAdmissible {k : Type uA} {B : Type vA} [Field k] [CommRing B] [Algebra k B]
    (A : Subalgebra k B) (m : Ideal B) : Prop :=
  IsArtinianRing A ∧ Algebra.EssFiniteType k A ∧
    ∃ (_ : IsLocalRing A),
      A.val.toRingHom.Flat ∧ (IsLocalRing.maximalIdeal A).map A.val.toRingHom = m

end Subalgebra
