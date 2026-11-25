/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ExternalProductExtendScalars
public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange

/-!

# Integral models with vanishing stalk at a point

Let `K` be a bounded constructible `ℚ̄_ℓ`-complex on `X` whose stalk at a rational point `x`
vanishes. Then `K` has an integral model `M` over some `𝒪_E` whose stalk at `x` vanishes as well
(`ProEtale.CondensedRing.exists_integralModel_isZero_upperStar`): take any integral model `K₀`
(`ProEtale.exists_padicAlgCl_iso_integralModel`) and replace it by its extension by zero
`j_! j^* K₀` from the complement of `x`; since `K_x = 0`, `K = j_! j^* K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Extension by zero from the complement of a point**: if the stalk `x^* K` of a bounded
constructible complex `K` at a rational point `x` vanishes, the counit `j_! j^* K ⟶ K` of the
adjunction `j_! ⊣ j^*` for the open complement `j : X ∖ {x} ⟶ X` is an isomorphism. Its
restriction to `X ∖ {x}` is an isomorphism by the triangle identity (the unit being an
isomorphism), and its restriction to `x` is a morphism between zero objects. -/
theorem isIso_counit_openImmersionLowerShriekUpperStarAdjunction_pointComplι
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (x : RationalPoint X) (K : Dᵇc(X.left)⟦Λ⟧)
    (hK : IsZero ((boundedConstructibleUpperStar Λ ℓ x).obj K)) :
    IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
      (pointComplι x)).counit.app K) := by
  set adj := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (pointComplι x)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : QuasiCompact (pointComplι x).left := inferInstanceAs (QuasiCompact (pointComplOpens x).ι)
  refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl Λ ℓ x (pointComplι x)
    (isCompl_range_pointComplι x).symm _ ?_ ?_
  · have : IsIso (adj.unit.app ((boundedConstructibleUpperStar Λ ℓ (pointComplι x)).obj K) ≫
        (boundedConstructibleUpperStar Λ ℓ (pointComplι x)).map (adj.counit.app K)) := by
      rw [adj.right_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app _) _
  · have hT := isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ
      (pointComplι x) x (isCompl_range_pointComplι x).disjoint
      ((boundedConstructibleUpperStar Λ ℓ (pointComplι x)).obj K)
    exact ⟨⟨hK.to_ _, hT.eq_of_src _ _, hK.eq_of_src _ _⟩⟩

/-- **Integral models with vanishing stalk**: a bounded constructible `ℚ̄_ℓ`-complex `K` with
`K_x = 0` at a rational point `x` has an integral model `M` over some `𝒪_E`, `ℚ̄_ℓ ⊗ M ≅ K`,
with `M_x = 0`. -/
theorem exists_integralModel_isZero_upperStar (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (x : RationalPoint X)
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    ∃ (E : FiniteIntermediateField ℓ) (M : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      Nonempty ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj M ≅ K) ∧
        IsZero ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ x).obj
          M) := by
  have := noetherianSpace_left_of_over X
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel X.left ℓ K
  have := isIso_counit_openImmersionLowerShriekUpperStarAdjunction_pointComplι
    (ℓ := ℓ) (Profinite.padicAlgClRingObj ℓ) x K hK
  refine ⟨E, (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.1)
    ℓ (pointComplι x)).obj
      ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ
        (pointComplι x)).obj K₀), ⟨?_⟩,
    isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ (pointComplι x) x
      (isCompl_range_pointComplι x).disjoint _⟩
  exact (constructibleToPadicAlgCl X.left ℓ E).mapIso
      ((boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E (pointComplι x)).app _) ≪≫
    (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E (pointComplι x)).app _ ≪≫
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointComplι x)).mapIso
      ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E (pointComplι x)).app K₀ ≪≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι x)).mapIso
          e) ≪≫
    asIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι x)).counit.app K)

end AlgebraicGeometry.ProEtale.CondensedRing
