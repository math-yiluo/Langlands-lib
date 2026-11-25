/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.FinitePointReflection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!

# Conservativity of derived finite pushforward to a separably closed point

Let `k` be a separably closed field and `p : Y ⟶ Spec k` a finite morphism. The derived
pushforward `Rp_*` on derived categories of `Λ`-modules on the pro-étale sites is conservative
(`ProEtale.CondensedRing.isIso_of_isIso_map_rightDerivedLowerStar_of_isFinite`): it is
triangulated, so it suffices that it reflects zero objects, and since `p_*` is exact,
`Hⁿ(Rp_* C) ≅ p_* Hⁿ(C)`, while `p_*` reflects zero objects
(`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_of_isFinite_of_isSepClosed`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section FiniteOverPoint

variable {k : Type u} [Field k] [IsSepClosed k] {Y : Scheme.{u}}

open scoped CategoryTheory.Functor in
/-- **Derived finite pushforward to a separably closed point is conservative**: for
`p : Y ⟶ Spec k` finite with `k` separably closed, a morphism `a` of complexes on `Y` such that
`Rp_* a` is an isomorphism is an isomorphism. Complete `a` to a distinguished triangle with third
object `C`; then `Rp_* C = 0`, so `p_* Hⁿ(C) ≅ Hⁿ(Rp_* C) = 0` for all `n`, hence `Hⁿ(C) = 0`
(`isZero_of_isZero_lowerStar_of_isFinite_of_isSepClosed`) and `C = 0`. -/
theorem isIso_of_isIso_map_rightDerivedLowerStar_of_isFinite (p : Y ⟶ Spec (.of k)) [IsFinite p]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))}
    (a : K ⟶ L) (h : IsIso ((R((p)_*⟦Λ⟧)).map a)) : IsIso a := by
  have : LocallyOfFinitePresentation p :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have := preservesFiniteColimits_lowerStar_of_isFinite Λ p
  obtain ⟨C, b, c, hT⟩ := distinguished_cocone_triangle a
  have hC : IsZero ((R((p)_*⟦Λ⟧)).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((R((p)_*⟦Λ⟧)).map_distinguished _ hT)).2 h
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (DerivedCategory.isZero_of_forall_isZero_homology C fun n ↦ ?_)
  exact isZero_of_isZero_lowerStar_of_isFinite_of_isSepClosed Λ p _
    (((DerivedCategory.homologyFunctor _ n).map_isZero hC).of_iso
      (((p)_*⟦Λ⟧.rightDerivedFunctorHomologyFunctorIso n).app C))

end FiniteOverPoint

end AlgebraicGeometry.ProEtale.CondensedRing
