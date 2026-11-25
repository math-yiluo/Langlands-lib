/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericDivisorGeneric
public import WeilConjectures.TraceFormula.Specialization.DefectLocal

/-!

# Generic vanishing of the defect near the generic points of the centre

Let `X` be a separated `k`-scheme of finite type, `Z = V(I) ⊆ X` a closed subscheme and
`g : V ⟶ X` an open immersion such that `Z ∩ V` is dense in `Z`, i.e. `V` contains every generic
point of `Z`. If the defect `C_{V, Z ∩ V}(g^* L)` vanishes generically on `Z ∩ V`, then
`C_{X,Z}(L)` vanishes generically on `Z`
(`ProEtale.CondensedRing.genericallyVanishingDefect_of_isOpenImmersion`). This is the reduction
"near a generic point `ζ` of `Z`" in the proof of blueprint
`lemma-vanishing-generic-points-principal-divisor--1`.

The proof uses the smooth exchange for the defect along `g`
(`ProEtale.CondensedRing.nonempty_specializationDefect_upperStar_iso`) and the identification of
the image in `N_⊥ Z` of the inverse image of an open `U' ⊆ Z ∩ V` with the inverse image of the
image of `U'`, the special fibres of the constant families forming a pullback square.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] {X V : Over (Spec (.of k))}
  (I : X.left.IdealSheafData)

/-- For an open immersion `g : V ⟶ X` and an open `U' ⊆ Z ∩ V`, the image in `N_⊥ Z` of the
inverse image of `U'` in `N_⊥ (Z ∩ V)` is the inverse image of the image of `U'` in `Z`. -/
lemma centreSpecialFibreMap_image_preimage (g : V ⟶ X) [IsOpenImmersion g.left]
    (U' : (centre V (I.comap g.left)).left.Opens) :
    (centreSpecialFibreMap g I k').left ''ᵁ
        (constantSpecialFibreProj k' (centre V (I.comap g.left)) ⁻¹ᵁ U') =
      constantSpecialFibreProj k' (centre X I) ⁻¹ᵁ ((centreMap g I).left ''ᵁ U') :=
  IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_centreSpecialFibreMap k' g I).flip U'

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

/-- Let `g : V ⟶ X` be an open immersion and `U' ⊆ Z ∩ V` open. If the restriction of the defect
`C_{V, Z ∩ V}(g^* L)` to the inverse image of `U'` vanishes, so does the restriction of
`C_{X,Z}(L)` to the inverse image of the image of `U'` in `Z`. -/
theorem isZero_restrict_specializationDefect_image (g : V ⟶ X) [IsOpenImmersion g.left]
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (U' : (centre V (I.comap g.left)).left.Opens)
    (hL : IsZero ((L((((constantSpecialFibreProj k' (centre V (I.comap g.left))) ⁻¹ᵁ
      U').ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      (specializationDefect V (I.comap g.left) k' (Profinite.padicAlgClRingObj ℓ)
        (L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L.obj)))) :
    IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ
      ((centreMap g I).left ''ᵁ U')).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) := by
  have e := (nonempty_specializationDefect_upperStar_iso g I k' L).some
  exact isZero_leftDerivedUpperStar_ι_obj_of_le (Profinite.padicAlgClRingObj ℓ)
    (centreSpecialFibreMap_image_preimage k' I g U').ge
    (isZero_leftDerivedUpperStar_image_ι_obj (Profinite.padicAlgClRingObj ℓ) _ _
      (hL.of_iso ((L(((constantSpecialFibreProj k' (centre V (I.comap g.left)) ⁻¹ᵁ
        U').ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso e.symm)))

/-- **Generic vanishing near the generic points of the centre**: let `g : V ⟶ X` be an open
immersion such that `Z ∩ V` is dense in `Z`. If the defect `C_{V, Z ∩ V}(g^* L)` vanishes
generically on `Z ∩ V`, then `C_{X,Z}(L)` vanishes generically on `Z`. -/
theorem genericallyVanishingDefect_of_isOpenImmersion (g : V ⟶ X) [IsOpenImmersion g.left]
    (hg : DenseRange (centreMap g I).left.base)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : genericallyVanishingDefect V (I.comap g.left) k' (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj L).obj) :
    genericallyVanishingDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj := by
  obtain ⟨U', hU', hL⟩ := h
  exact ⟨(centreMap g I).left ''ᵁ U', hg.dense_image (centreMap g I).left.continuous hU',
    isZero_restrict_specializationDefect_image k' I g L U' hL⟩

end AlgebraicGeometry.ProEtale.CondensedRing
