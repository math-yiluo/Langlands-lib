/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceOpenComp
public import WeilConjectures.TraceFormula.Specialization.NearbyExceptionalExchangeSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyTwistCompat
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityTwistAssembly
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingCompositionLaw
import WeilConjectures.Tactic.TransportExact

/-!

# The twist equation along a slice morphism and the composition law

Let `b̄ : M ⟶ P` be a morphism of proper trait models with full generic fibres over a common
generic base `(F, ι)`, over proper `b̄₁ : X₁ ⟶ Z₁` and `b̄₂ : X' ⟶ Z'`, and let
`φ'' : M'' ⟶ P''` be a morphism of proper trait models with full generic fibres over a common
generic base `(F₂, ι₂)` (over another trait), over proper `i₁''`, `i₂''`. Let `s : M'' ⟶ M` and
`s_P : P'' ⟶ P` be morphisms of models with `s ≫ b̄ = φ'' ≫ s_P` and cartesian squares of bases
and of special fibres.

The *twist equation of `θ_M` along `s`*,
`p^* θ_M ≫ v = α_s ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T` (`α_s` the pullback exchange of `s`,
`κ` the twist isomorphism of `M''`, `T = ℚ̄_ℓ(0)[2]`), follows from the same equation for `θ_P`
along `s_P`, provided the base change maps `γ` of the exceptional inverse images `Rb̄₁^!`, `Rb̄₂^!`
along `s` are invertible at the dualizing complexes
(`NearbyCyclesModel.exists_twist_of_slice_of_composition_law`).

This is `NearbyCyclesModel.exists_twist_of_composition_law` for the composition laws of `θ` along
`b̄` and `φ''` (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law`), the slicing
square of their exceptional exchanges (`NearbyCyclesModel.Hom.exceptionalExchange_slice_app`) and
the twist compatibility of the exceptional exchange of `φ''`
(`NearbyCyclesModel.exceptionalExchange_zeroTwistIso`).

It is meant for `P = ℙ¹_S` (`NearbyCyclesModel.projectiveLineModel`), `M` a proper model with a
proper coordinate `b̄ : M ⟶ ℙ¹_S`, `M''` the generic slice of the open sub-model
`W = b̄⁻¹(𝔸¹_S)` along `b̄|_W` with `s : M'' ⟶ W ⟶ M`, and `P''` the slice trait `Spec K⟦t⟧` as a
model of its generic point, mapping to `ℙ¹_S` through `𝔸¹_S`; the conclusion is then the
hypothesis of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel_comp`.
The statement is kept over abstract fields, so that the two presentations of the fields of
fractions `Frac k'⟦t⟧` (`OreLocalization.instCommRing` and `Field.toCommRing`) are never compared
inside it.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {K : Type u} [Field K] [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  {F₂ : Type u} [Field F₂] [Fact (ringChar F₂).Prime] [Fact (ringChar F₂ ≠ ℓ)]
  {ι₂ : Spec (.of (FractionRing (PowerSeries K))) ⟶ Spec (.of F₂)}
  {X₁ Z₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
  [IsSeparated X₁.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom] [IsSeparated Z₁.hom]
  [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint Z₁).left]
  {X' Z' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [IsProper (CondensedRing.toPoint X').left] [IsProper (CondensedRing.toPoint Z').left]
  {X₂ Z₂ : Over (Spec (.of F₂))} [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom]
  [IsSeparated X₂.hom] [LocallyOfFiniteType Z₂.hom] [QuasiCompact Z₂.hom] [IsSeparated Z₂.hom]
  [IsProper (CondensedRing.toPoint X₂).left] [IsProper (CondensedRing.toPoint Z₂).left]
  {X'' Z'' : Over (Spec (.of K))} [LocallyOfFiniteType X''.hom] [QuasiCompact X''.hom]
  [IsSeparated X''.hom] [LocallyOfFiniteType Z''.hom] [QuasiCompact Z''.hom]
  [IsSeparated Z''.hom]
  [IsProper (CondensedRing.toPoint X'').left] [IsProper (CondensedRing.toPoint Z'').left]
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {P : NearbyCyclesModel Z₁.left Z'.left} {qP : P.total ⟶ trait k'}
  {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
  {M'' : NearbyCyclesModel X₂.left X''.left} {q'' : M''.total ⟶ trait K}
  {g'' : M''.generic ⟶ Spec (.of (traitGenericField K))}
  {P'' : NearbyCyclesModel Z₂.left Z''.left} {qP'' : P''.total ⟶ trait K}
  {gP'' : P''.generic ⟶ Spec (.of (traitGenericField K))}

/-- **The twist equation along a slice morphism and the composition law**: in the situation of
the module docstring, the twist equation of `θ_P` along `s_P` implies that of `θ_M` along `s`,
with `u = C(ρ⁻¹) ≪≫ γ_b ≪≫ Ri₁''^!(u_P) ≪≫ n ≪≫ ρ₂ ▷ T` and
`v = P(ρ'⁻¹) ≪≫ γ_s ≪≫ Ri₂''^!(v_P) ≪≫ m ≪≫ ρ₂' ▷ T`. -/
theorem exists_twist_of_slice_of_composition_law (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase K ℓ)
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hP : P.IsTraitModelOfGenericBase Z₁ ι qP gP) [IsProper qP]
    (hPgen : IsPullback P.ε gP Z₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hM'' : M''.IsTraitModelOfGenericBase X₂ ι₂ q'' g'') [IsProper q'']
    (hM''gen : IsPullback M''.ε g'' X₂.hom (traitGenericPointToSpec K ≫ ι₂))
    (hP'' : P''.IsTraitModelOfGenericBase Z₂ ι₂ qP'' gP'') [IsProper qP'']
    (hP''gen : IsPullback P''.ε gP'' Z₂.hom (traitGenericPointToSpec K ≫ ι₂))
    (b₁ : X₁ ⟶ Z₁) [IsProper b₁.left] (b₂ : X' ⟶ Z') [IsProper b₂.left]
    (b : M.Hom P b₁.left b₂.left) (hq : q = b.total ≫ qP) (hg : g = b.generic ≫ gP)
    (i₁ : X₂ ⟶ Z₂) [IsProper i₁.left] (i₂ : X'' ⟶ Z'') [IsProper i₂.left]
    (φ : M''.Hom P'' i₁.left i₂.left) (hq'' : q'' = φ.total ≫ qP'')
    (hg'' : g'' = φ.generic ≫ gP'')
    {c : X₂.left ⟶ X₁.left} {p : X''.left ⟶ X'.left} (s : M''.Hom M c p)
    {cP : Z₂.left ⟶ Z₁.left} {pP : Z''.left ⟶ Z'.left} (sP : P''.Hom P cP pP)
    (htot : s.total ≫ b.total = φ.total ≫ sP.total)
    (hgen : s.generic ≫ b.generic = φ.generic ≫ sP.generic)
    (hbsq : IsPullback c i₁.left b₁.left cP) (hssq : IsPullback p i₂.left b₂.left pP)
    [IsIso ((upperShriekBaseChangeOfMap ℓ hbsq).app (dualizingComplex ℓ Z₁))]
    [IsIso ((upperShriekBaseChangeOfMap ℓ hssq).app (dualizingComplex ℓ Z'))]
    (HP : ∃ (uP : (boundedConstructibleUpperStarOfMap ℓ (X := Z₁) (Y := Z₂) cP).obj
          (dualizingComplex ℓ Z₁) ≅
        dualizingComplex ℓ Z₂ ⊗ boundedConstructibleTateTwist ℓ Z₂ 0 2)
      (vP : (boundedConstructibleUpperStarOfMap ℓ (X := Z') (Y := Z'') pP).obj
          (dualizingComplex ℓ Z') ≅
        dualizingComplex ℓ Z'' ⊗ boundedConstructibleTateTwist ℓ Z'' 0 2),
      (boundedConstructibleUpperStarOfMap ℓ (X := Z') (Y := Z'') pP).map (D.θ hP) ≫ vP.hom =
        (sP.boundedConstructiblePullbackExchangeOfMap ℓ
            (hP''.preservesBoundedConstructible (ℓ := ℓ))
            (hP.preservesBoundedConstructible (ℓ := ℓ))).app (dualizingComplex ℓ Z₁) ≫
          (boundedConstructibleNearbyCycles (hP''.preservesBoundedConstructible (ℓ := ℓ))).map
            uP.hom ≫
          (P''.zeroTwistIso (hP''.preservesBoundedConstructible (ℓ := ℓ)) qP'' 2
            (dualizingComplex ℓ Z₂)).hom ≫
          DK.θ hP'' ▷ boundedConstructibleTateTwist ℓ Z'' 0 2) :
    ∃ (u : (boundedConstructibleUpperStarOfMap ℓ (X := X₁) (Y := X₂) c).obj
          (dualizingComplex ℓ X₁) ≅
        dualizingComplex ℓ X₂ ⊗ boundedConstructibleTateTwist ℓ X₂ 0 2)
      (v : (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := X'') p).obj
          (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ X'' ⊗ boundedConstructibleTateTwist ℓ X'' 0 2),
      (boundedConstructibleUpperStarOfMap ℓ (X := X') (Y := X'') p).map (D.θ hM) ≫ v.hom =
        (s.boundedConstructiblePullbackExchangeOfMap ℓ
            (hM''.preservesBoundedConstructible (ℓ := ℓ))
            (hM.preservesBoundedConstructible (ℓ := ℓ))).app (dualizingComplex ℓ X₁) ≫
          (boundedConstructibleNearbyCycles (hM''.preservesBoundedConstructible (ℓ := ℓ))).map
            u.hom ≫
          (M''.zeroTwistIso (hM''.preservesBoundedConstructible (ℓ := ℓ)) q'' 2
            (dualizingComplex ℓ X₂)).hom ≫
          DK.θ hM'' ▷ boundedConstructibleTateTwist ℓ X'' 0 2 := by
  -- the composition laws along `b̄` and `φ''`
  have hθ := D.θ_comp_law hP hM hPgen hMgen b₁ b₂ b hq hg
  have hθ'' := DK.θ_comp_law hP'' hM'' hP''gen hM''gen i₁ i₂ φ hq'' hg''
  -- the slicing square of the exceptional exchanges
  have := IsTraitModelOfGenericBase.isIso_boundedConstructiblePushforwardExchange ℓ hP hM hPgen
    hMgen b₁ b₂ b hq hg
  have := IsTraitModelOfGenericBase.isIso_boundedConstructiblePushforwardExchange ℓ hP'' hM''
    hP''gen hM''gen i₁ i₂ φ hq'' hg''
  have hsq := Hom.exceptionalExchange_slice_app ℓ
    (hP.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ))
    (hP''.preservesBoundedConstructible (ℓ := ℓ)) (hM''.preservesBoundedConstructible (ℓ := ℓ))
    b φ sP s htot hgen
    (sP.boundedConstructiblePullbackExchangeOfMap ℓ (hP''.preservesBoundedConstructible (ℓ := ℓ))
      (hP.preservesBoundedConstructible (ℓ := ℓ)))
    (fun A ↦ by
      have := Hom.boundedConstructiblePullbackExchangeOfMap_app_hom ℓ sP
        (hP''.preservesBoundedConstructible (ℓ := ℓ)) (hP.preservesBoundedConstructible (ℓ := ℓ)) A
      transport_exact this)
    (s.boundedConstructiblePullbackExchangeOfMap ℓ (hM''.preservesBoundedConstructible (ℓ := ℓ))
      (hM.preservesBoundedConstructible (ℓ := ℓ)))
    (fun A ↦ by
      have := Hom.boundedConstructiblePullbackExchangeOfMap_app_hom ℓ s
        (hM''.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ)) A
      transport_exact this) hbsq hssq
    _ (IsTraitModelOfGenericBase.pushforwardExchange_app_comp_properCompactSupportExchange_app ℓ
      hP hM hPgen hMgen b₁ b₂ b hq hg)
    _ (IsTraitModelOfGenericBase.pushforwardExchange_app_comp_properCompactSupportExchange_app ℓ
      hP'' hM'' hP''gen hM''gen i₁ i₂ φ hq'' hg'')
    (dualizingComplex ℓ Z₁)
  -- the twists and the exceptional exchange of `φ''`
  have hκP := exceptionalExchange_zeroTwistIso φ (hP''.preservesBoundedConstructible (ℓ := ℓ))
    (hM''.preservesBoundedConstructible (ℓ := ℓ)) qP'' q'' _
    (IsTraitModelOfGenericBase.pushforwardExchange_app_comp_properCompactSupportExchange_app ℓ
      hP'' hM'' hP''gen hM''gen i₁ i₂ φ hq'' hg'') 2 (dualizingComplex ℓ Z₂)
  exact exists_twist_of_composition_law _ (D.θ hM) _ _ _ _ _ hθ _ _ _ hθ''
    (s.boundedConstructiblePullbackExchangeOfMap ℓ (hM''.preservesBoundedConstructible (ℓ := ℓ))
      (hM.preservesBoundedConstructible (ℓ := ℓ)))
    (sP.boundedConstructiblePullbackExchangeOfMap ℓ (hP''.preservesBoundedConstructible (ℓ := ℓ))
      (hP.preservesBoundedConstructible (ℓ := ℓ)))
    (upperShriekBaseChangeOfMap ℓ hbsq) (upperShriekBaseChangeOfMap ℓ hssq) (by transport_exact hsq)
    (fun Z ↦ upperShriekZeroTwistIso ℓ i₂ 2 Z)
    (fun f ↦ upperShriekZeroTwistIso_hom_naturality ℓ i₂ 2 f)
    (upperShriekZeroTwistIso ℓ i₁ 2 _) _
    (M''.zeroTwistIso (hM''.preservesBoundedConstructible (ℓ := ℓ)) q'' 2)
    (fun f ↦ zeroTwistIso_hom_naturality _ _ 2 f) hκP HP

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
