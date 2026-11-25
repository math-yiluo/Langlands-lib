/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperStarProducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedAdicCompleteRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarMapModLimits
public import WeilConjectures.TraceFormula.OpenCover

/-!
# Constructible `𝒪_E`-module objects are derived complete

Let `X` be a noetherian scheme. A constructible `𝒪_{E,X}`-module object `M` on `X_proét` is
derived `ℓ`-adically complete (`ProEtale.isDerivedAdicComplete_of_isConstructibleModuleObject`).

As in the proof of Nakayama's lemma for constructible module objects
(`ProEtale.isZero_of_isConstructibleModuleObject_of_isZero_extendScalars`), there is a finite
jointly surjective family of quasi-compact morphisms `g : V ⟶ X`, composites of the inclusion of
an affine open, a member of a pro-étale cover and the immersion of a stratum, such that every
`g^* M` is finitely presented, hence derived complete
(`ProEtale.isDerivedAdicComplete_of_isFinitelyPresented`). The pullbacks `g^*` jointly reflect
isomorphisms (`ProEtale.CondensedRing.jointlyReflectIsomorphisms_upperStar_of_cover`) and
commute with countable products: pullbacks along weakly étale morphisms preserve all limits, and
pullbacks along immersions into noetherian schemes preserve countable products
(`ProEtale.CondensedRing.preservesLimitsOfShape_upperStar_of_isImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Pullback of module objects along a weakly étale morphism preserves all limits: it is the
pullback of the underlying sheaves, which is a restriction, followed by the extension of
scalars along the isomorphism `α_g`. -/
instance preservesLimitsOfShape_upperStar_of_weaklyEtale {U X : Scheme.{u}} (g : U ⟶ X)
    [WeaklyEtale g] (J : Type*) [Category* J] [HasLimitsOfShape J Ab.{u + 1}] :
    PreservesLimitsOfShape J (g)^*⟦Λ⟧ :=
  have : PreservesLimitsOfShape J (Mod.extendScalars (condensedPullbackHom Λ g)) :=
    preservesLimitsOfShape_of_natIso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).symm
  comp_preservesLimitsOfShape _ _

/-- If the pullbacks along `f` and `g` preserve limits of shape `J`, so does the pullback along
`f ≫ g`. -/
lemma preservesLimitsOfShape_upperStar_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (J : Type*) [Category* J] [PreservesLimitsOfShape J (f)^*⟦Λ⟧]
    [PreservesLimitsOfShape J (g)^*⟦Λ⟧] : PreservesLimitsOfShape J (f ≫ g)^*⟦Λ⟧ :=
  preservesLimitsOfShape_of_natIso (upperStarComp Λ f g).symm

/-- On a scheme with noetherian underlying space, the pullback of module objects along a closed
immersion preserves countable products: the open complement is quasi-compact. -/
theorem preservesLimitsOfShape_upperStar_of_isClosedImmersion {Z X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesLimitsOfShape (Discrete ℕ) (i)^*⟦Λ⟧ := by
  let V : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact preservesLimitsOfShape_upperStar_of_isCompl Λ i V.ι (by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl)

/-- On a scheme with noetherian underlying space, the pullback of module objects along an
immersion preserves countable products: an immersion is a closed immersion into an open
subscheme, followed by the inclusion of the open subscheme. -/
theorem preservesLimitsOfShape_upperStar_of_isImmersion {Y X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (f : Y ⟶ X) [IsImmersion f] :
    PreservesLimitsOfShape (Discrete ℕ) (f)^*⟦Λ⟧ := by
  have : TopologicalSpace.NoetherianSpace f.coborderRange :=
    f.coborderRange.ι.isOpenEmbedding.isInducing.noetherianSpace
  have := preservesLimitsOfShape_upperStar_of_isClosedImmersion Λ f.liftCoborder
  have := preservesLimitsOfShape_upperStar_comp Λ f.liftCoborder f.coborderRange.ι (Discrete ℕ)
  rwa [f.liftCoborder_ι] at this

end CondensedRing

open CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- Let `i : Y ⟶ X` and `f : U ⟶ Y` be morphisms such that the restriction of `M` to `Y`,
further restricted along `f`, is finitely presented. Then for every open `W ⊆ U`, the pullback
of `M` along `W ⟶ U ⟶ Y ⟶ X` is finitely presented. -/
lemma isFinitelyPresented_upperStar_opens_ι_comp {X Y U : Scheme.{u}} (i : Y ⟶ X) (f : U ⟶ Y)
    (W : U.Opens) (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
    (h : Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} f).obj
      ((ProEtale.upperStar Ab.{u + 1} i).obj
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj
        (((ProEtale.upperStar Ab.{u + 1} i).mapMod _).obj M))) :
    Mod.IsFinitelyPresented _
      ((W.ι ≫ f ≫ i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.obj M) := by
  have h₁ := isFinitelyPresented_upperStar_of_comap_iso (Profinite.padicIntegersRingObj ℓ E.1)
    f (condensedPullbackHom _ i) (comapUpperStarObjIso _ i M) h
  exact (CondensedRing.IsFinitelyPresented.upperStar _ W.ι h₁).of_iso
    ((W.ι)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.mapIso
      ((CondensedRing.upperStarComp _ f i).app M).symm ≪≫
      ((CondensedRing.upperStarComp _ W.ι (f ≫ i)).app M).symm)

/-- The composite `W ⟶ U ⟶ Y ⟶ X` of the inclusion of an affine open, a morphism and a
morphism from a quasi-compact scheme is quasi-compact. -/
lemma quasiCompact_opens_ι_comp {X Y U : Scheme.{u}} [IsNoetherian X] (i : Y ⟶ X) (f : U ⟶ Y)
    (W : U.Opens) (hW : IsAffine W) : QuasiCompact (W.ι ≫ f ≫ i) :=
  quasiCompact_of_compactSpace _

/-- A point `i (f z)` with `z ∈ W` lies in the range of `W ⟶ U ⟶ Y ⟶ X`. -/
lemma mem_range_opens_ι_comp {X Y U : Scheme.{u}} (i : Y ⟶ X) (f : U ⟶ Y) (W : U.Opens)
    {z : U} (hz : z ∈ W) : i.base (f.base z) ∈ Set.range (W.ι ≫ f ≫ i).base := by
  obtain ⟨w, rfl⟩ : z ∈ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hz
  exact ⟨w, by simp only [Scheme.Hom.comp_base, TopCat.comp_app]⟩

/-- On a noetherian scheme `X`, the pullback along the composite `W ⟶ U ⟶ Y ⟶ X` of the
inclusion of an open, a weakly étale morphism and an immersion preserves countable products. -/
lemma preservesLimitsOfShape_upperStar_opens_ι_comp {X Y U : Scheme.{u}} [IsNoetherian X]
    (i : Y ⟶ X) [IsImmersion i] (f : U ⟶ Y) (hf : WeaklyEtale f) (W : U.Opens) :
    PreservesLimitsOfShape (Discrete ℕ)
      (W.ι ≫ f ≫ i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧ := by
  have := CondensedRing.preservesLimitsOfShape_upperStar_of_isImmersion
    (Profinite.padicIntegersRingObj ℓ E.1) i
  have := CondensedRing.preservesLimitsOfShape_upperStar_comp
    (Profinite.padicIntegersRingObj ℓ E.1) f i (Discrete ℕ)
  exact CondensedRing.preservesLimitsOfShape_upperStar_comp _ _ _ _

/-- **Constructible `𝒪_E`-module objects are derived complete**: on a noetherian scheme `X`, a
constructible `𝒪_{E,X}`-module object is derived `ℓ`-adically complete. Finitely many affine opens
`W` of members of pro-étale covers of the strata of `X` cover `X`, the pullbacks of `M` to them
are finitely presented, hence derived complete
(`ProEtale.isDerivedAdicComplete_of_isFinitelyPresented`), and these pullbacks preserve countable
products and jointly reflect isomorphisms. -/
theorem isDerivedAdicComplete_of_isConstructibleModuleObject {X : Scheme.{u}} [IsNoetherian X]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
    (hM : IsConstructibleModuleObject _ M) : IsDerivedAdicComplete (ℓ : ℤ) M := by
  obtain ⟨S, hS⟩ := hM
  choose 𝒰 h𝒰 using hS
  -- the strata are quasi-compact
  have hc (a : Fin S.n) : CompactSpace (S.domain a) := by
    have := (S.immersion a).isEmbedding.isInducing.noetherianSpace
    infer_instance
  -- finitely many affine opens of members of the covers cover each stratum
  have hqc (a : Fin S.n) : QuasiCompactCover (𝒰 a).toPreZeroHypercover := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact (show _ ∈ propQCPrecoverage @WeaklyEtale _ from (𝒰 a).mem₀).1
  have hfin (a : Fin S.n) := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    (𝒰 a).toPreZeroHypercover (U := ⊤) (by simpa using isCompact_univ)
  choose N j W hW hcov using hfin
  have hwe (a : Fin S.n) (i : (𝒰 a).I₀) : WeaklyEtale ((𝒰 a).f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ (𝒰 a).mem₀ (.mk i)
  have hg : ∀ x, ∃ p : Σ a : Fin S.n, Fin (N a),
      x ∈ Set.range ((W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1).base := by
    intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    rw [← S.range_immersion a] at ha
    obtain ⟨y, rfl⟩ := ha
    have hy : y ∈ ⋃ i, (𝒰 a).f (j a i) '' (W a i) := by
      rw [hcov a]
      trivial
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
    exact ⟨⟨a, i⟩, mem_range_opens_ι_comp _ _ (W a i) hz⟩
  have hfp (a : Fin S.n) (i : Fin (N a)) : Mod.IsFinitelyPresented _ ((((W a i).ι ≫
      (𝒰 a).f (j a i) ≫ S.immersion a))^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.obj M) := by
    have h₁ := isFinitelyPresented_upperStar_of_comap_iso (Profinite.padicIntegersRingObj ℓ E.1)
      ((𝒰 a).f (j a i)) (condensedPullbackHom _ (S.immersion a))
      (comapUpperStarObjIso _ (S.immersion a) M) (h𝒰 a (j a i))
    exact (CondensedRing.IsFinitelyPresented.upperStar _ (W a i).ι h₁).of_iso
      (((W a i).ι)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.mapIso
        ((CondensedRing.upperStarComp _ ((𝒰 a).f (j a i)) (S.immersion a)).app M).symm ≪≫
        ((CondensedRing.upperStarComp _ (W a i).ι ((𝒰 a).f (j a i) ≫ S.immersion a)).app M).symm)
  have := fun p : Σ a : Fin S.n, Fin (N a) ↦
    preservesLimitsOfShape_upperStar_opens_ι_comp ℓ E (S.immersion p.1) _
      (hwe p.1 (j p.1 p.2)) (W p.1 p.2)
  refine IsDerivedAdicComplete.of_map
    (fun p : Σ a : Fin S.n, Fin (N a) ↦ CondensedRing.upperStar
      (Profinite.padicIntegersRingObj ℓ E.1)
      ((W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1))
    (fun φ hφ ↦ ?_) fun p ↦ isDerivedAdicComplete_of_isFinitelyPresented ℓ E _ (hfp p.1 p.2)
  have := hφ
  have : ∀ p : Σ a : Fin S.n, Fin (N a),
      QuasiCompact ((W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1) :=
    fun p ↦ quasiCompact_opens_ι_comp _ _ _ (hW p.1 p.2)
  exact (CondensedRing.jointlyReflectIsomorphisms_upperStar_of_cover _ _ hg).isIso φ

end AlgebraicGeometry.ProEtale
