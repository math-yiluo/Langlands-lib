/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase

/-!

# Finiteness for trait models over a generic base

Let `M` be a trait model of an `F`-scheme `X₁` over the generic base `(F, X₁)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`): a model of finite type over the strictly
henselian trait `S = Spec k'⟦t⟧` whose generic fibre `𝒳_η = 𝒳 ×_S η` maps to `X₁` (by an open
immersion into `X₁ ×_F η`) compatibly with `ε`. Its nearby cycles `Ψ = Li^* Rj_* Lε^*` preserve
bounded constructible complexes
(`NearbyCyclesModel.IsTraitModelOfGenericBase.preservesBoundedConstructible`).

Unlike `NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`, the identification `ε`
need not factor through the total space `𝒳`, only through the generic fibre `𝒳_η`, which is open
in `𝒳` as `η` is open in `S`. For bounded constructible `K` on `X₁`, let `A` be its pullback to
`𝒳_η` and `B = v_! A` its extension by zero along the open immersion `v : 𝒳_η ⟶ 𝒳`, bounded
constructible on `𝒳`. As `j : 𝒳_Ω ⟶ 𝒳` factors through `v`, `Lj^* B ≅ Lε^* K`, so
`Ψ K ≅ Li^* Rj_* Lj^* B` is bounded constructible by Deligne's finiteness theorem
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {X' : Over (Spec (.of k'))}
  {F : Type u} [Field F]

/-- **Deligne's finiteness theorem for trait models over a generic base**: the nearby cycles
`Ψ = Li^* Rj_* Lε^*` of a trait model over the generic base `(F, X₁)` preserve bounded
constructible complexes. For bounded constructible `K` on `X₁`, its pullback `A` to the generic
fibre `𝒳_η` extends by zero along the open immersion `v : 𝒳_η ⟶ 𝒳` to a bounded constructible
`B = v_! A` on `𝒳` with `Lj^* B ≅ Lε^* K`, as `j` factors through `v` and `Lv^* v_! A ≅ A`; so
`Ψ K ≅ Li^* Rj_* Lj^* B` is bounded constructible
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`). -/
theorem IsTraitModelOfGenericBase.preservesBoundedConstructible {X₁ : Over (Spec (.of F))}
    {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) := by
  obtain ⟨w, -, -, hw⟩ := h.exists_openImmersion_genericFibre
  have hM := h.isTraitModelOver.isTraitModel
  have := hM.isNoetherian_total
  intro K hK
  let v := pullback.fst q (traitGenericSpec k')
  let s := genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w
  let A := (L((w ≫ pullback.fst _ _)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K
  have hB := boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj
    (Profinite.padicAlgClRingObj ℓ) v A
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ K hK)
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) v).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have e₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ)
    (genericFibreInclusion_fst M q g h.isTraitModelOver.isPullback_j.w).symm
    ((D((v)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A)).some
  have e₂ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) s v).app
    ((D((v)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A)
  have e₃ := (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
    (Profinite.padicAlgClRingObj ℓ) v).app ((D((v)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A)
  have e₄ := asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) v).unit.app A)
  have e₅ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) s
    (w ≫ pullback.fst _ _)).app K
  have e₆ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ) hw K).some
  exact (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      X'.left)).prop_of_iso
    ((L((M.i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso
      ((R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso (e₁ ≪≫ e₂ ≪≫
        (L((s)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso (e₃ ≪≫ e₄.symm) ≪≫ e₅.symm ≪≫ e₆)))
    (boundedConstructible_geometricNearbyCycles_obj M hM hB)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
