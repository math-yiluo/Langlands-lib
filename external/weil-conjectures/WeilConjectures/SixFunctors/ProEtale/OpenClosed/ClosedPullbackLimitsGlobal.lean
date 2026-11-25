/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimits

/-!
# The closed inverse image preserves limits: the global case

Let `X` be quasi-compact and quasi-separated, and `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j`. The pullback `i^*` of pro-étale sheaves of modules preserves
all small limits (`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isCompl`,
blueprint `proposition-extension-zero-restriction-closed-subscheme`). The affine case `X = Spec A`
is `AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_closedSpecι`; in general the
comparison map `i^* lim F ⟶ lim i^* F` is an isomorphism after restriction to the closed fibres
of the members of a finite affine open cover of `X`, which jointly detect isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {R : Type (u + 1)} [Ring R]

/-- The pullback along a weakly étale monomorphism (e.g. an open immersion or an isomorphism)
preserves limits: it is the restriction to the localized site, a right adjoint. -/
lemma preservesLimitsOfSize_upperStar_of_mono {Y X : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    [Mono g] : PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[ModuleCat.{u + 1} R]) :=
  preservesLimits_of_natIso (upperStarIsoLocalizationRestriction _ g inferInstance).symm

/-- A morphism of pro-étale sheaves of modules whose pullbacks along finitely many quasi-compact
morphisms jointly covering the base are isomorphisms is an isomorphism. -/
lemma isIso_of_forall_isIso_upperStar_map {U : Scheme.{u}} {κ : Type*} [Finite κ]
    {Z : κ → Scheme.{u}} (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)]
    (hg : ∀ x, ∃ k, x ∈ Set.range (g k)) {F G : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)}
    (φ : F ⟶ G) (h : ∀ k, IsIso ((g k)^*[ModuleCat.{u + 1} R].map φ)) : IsIso φ := by
  have hzero : ∀ E : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R),
      (∀ k, IsZero ((g k)^*[ModuleCat.{u + 1} R].obj E)) → IsZero E := fun E hE ↦
    (IsZero.iff_id_eq_zero E).2 (eq_zero_of_forall_upperStar_map_eq_zero R g hg (𝟙 E)
      fun k ↦ (hE k).eq_of_src _ _)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _ (hzero _ fun k ↦
    have := h k
    (isZero_kernel_of_mono ((g k)^*[ModuleCat.{u + 1} R].map φ)).of_iso
      (PreservesKernel.iso _ φ))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _ (hzero _ fun k ↦
    have := h k
    (isZero_cokernel_of_epi ((g k)^*[ModuleCat.{u + 1} R].map φ)).of_iso
      (PreservesCokernel.iso _ φ))
  exact isIso_of_mono_of_epi φ

/-- The pullback along a composite `h₁ ≫ h₂` preserves limits if the pullbacks along `h₁` and
`h₂` do. -/
lemma preservesLimitsOfSize_upperStar_comp {T S X : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ X)
    [PreservesLimitsOfSize.{u + 1, u + 1} ((h₁)^*[ModuleCat.{u + 1} R])]
    [PreservesLimitsOfSize.{u + 1, u + 1} ((h₂)^*[ModuleCat.{u + 1} R])] :
    PreservesLimitsOfSize.{u + 1, u + 1} ((h₁ ≫ h₂)^*[ModuleCat.{u + 1} R]) :=
  preservesLimits_of_natIso (upperStarComp _ h₁ h₂).symm

/-- Composing with an isomorphism does not change complementarity of ranges. -/
lemma isCompl_range_comp_iso {Z U X Y : Scheme.{u}} {i : Z ⟶ X} {j : U ⟶ X} (e : X ≅ Y)
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    IsCompl (Set.range (i ≫ e.hom).base) (Set.range (j ≫ e.hom).base) := by
  have hb : Function.Bijective e.hom.base :=
    ⟨(Scheme.Hom.homeomorph e.hom).injective, (Scheme.Hom.homeomorph e.hom).surjective⟩
  have hr : ∀ {W : Scheme.{u}} (k : W ⟶ X), Set.range (k ≫ e.hom).base =
      e.hom.base '' Set.range k.base := fun k ↦ by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [hr, hr, hij.compl_eq.symm, Set.image_compl_eq hb]
  exact isCompl_compl

variable {Z U : Scheme.{u}}

/-- The closed inverse image preserves limits for a closed immersion into an affine scheme with
quasi-compact open complement. -/
lemma preservesLimitsOfSize_upperStar_of_isAffine {Y : Scheme.{u}} [IsAffine Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesLimitsOfSize.{u + 1, u + 1} ((i)^*[ModuleCat.{u + 1} R]) := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := i ≫ Y.isoSpec.hom)).1 inferInstance
  have hij' := isCompl_range_comp_iso Y.isoSpec hij
  rw [he] at hij'
  have h₁ : Set.range (e.hom ≫ closedSpecι I).base = Set.range (closedSpecι I).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Function.Surjective.range_comp (Scheme.Hom.homeomorph e.hom).surjective _
  rw [h₁] at hij'
  have : PreservesLimitsOfSize.{u + 1, u + 1} ((closedSpecι I)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_closedSpecι I (j ≫ Y.isoSpec.hom) hij'
  have : PreservesLimitsOfSize.{u + 1, u + 1} ((e.hom)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_of_mono e.hom
  have : PreservesLimitsOfSize.{u + 1, u + 1} ((Y.isoSpec.inv)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_of_mono Y.isoSpec.inv
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      ((e.hom ≫ closedSpecι I)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_comp e.hom (closedSpecι I)
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (((e.hom ≫ closedSpecι I) ≫ Y.isoSpec.inv)^*[ModuleCat.{u + 1} R]) :=
    preservesLimitsOfSize_upperStar_comp _ _
  have hi : (e.hom ≫ closedSpecι I) ≫ Y.isoSpec.inv = i := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact preservesLimits_of_natIso
    (eqToIso (congrArg (fun f ↦ (f)^*[ModuleCat.{u + 1} R]) hi))

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme` (subsection
`proposition-extension-zero-restriction-closed-subscheme`), part (2): let `X` be quasi-compact and
quasi-separated and `i : Z ⟶ X` a closed immersion with quasi-compact open complement `j`. The
pullback `i^*` of pro-étale sheaves of modules preserves all small limits. (It preserves all
colimits, being a left adjoint, and it is exact.)

Over a finite affine open cover `X = ⋃ Xₖ` this is
`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isAffine`, and the restrictions
to the closed fibres `Zₖ = Z ×_X Xₖ` jointly detect isomorphisms
(`AlgebraicGeometry.ProEtale.isIso_of_forall_isIso_upperStar_map`). -/
theorem preservesLimitsOfSize_upperStar_of_isCompl {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesLimitsOfSize.{u + 1, u + 1} ((i)^*[ModuleCat.{u + 1} R]) := by
  refine ⟨fun {J} _ ↦ ⟨fun {D} ↦ ?_⟩⟩
  let 𝒰 := X.affineCover.finiteSubcover
  let o (k : 𝒰.I₀) := 𝒰.f k
  have hk (k : 𝒰.I₀) : PreservesLimitsOfSize.{u + 1, u + 1}
      ((pullback.snd i (o k))^*[ModuleCat.{u + 1} R]) := by
    refine preservesLimitsOfSize_upperStar_of_isAffine (pullback.snd i (o k))
      (pullback.snd j (o k)) ?_
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
    exact hij.preimage _
  have hc (k : 𝒰.I₀) : IsIso ((pullback.fst i (o k))^*[ModuleCat.{u + 1} R].map
      (limit.post D (i)^*[ModuleCat.{u + 1} R])) := by
    have := hk k
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        ((pullback.fst i (o k))^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfSize_upperStar_of_mono _
    have : PreservesLimitsOfSize.{u + 1, u + 1} ((o k)^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfSize_upperStar_of_mono _
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        ((pullback.snd i (o k) ≫ o k)^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfSize_upperStar_comp _ _
    have : PreservesLimit D ((i)^*[ModuleCat.{u + 1} R] ⋙
        (pullback.fst i (o k))^*[ModuleCat.{u + 1} R]) :=
      preservesLimit_of_natIso D (eqToIso (congrArg (fun f ↦ (f)^*[ModuleCat.{u + 1} R])
        pullback.condition.symm) ≪≫ upperStarComp _ (pullback.fst i (o k)) i)
    have h := limit.post_post D (i)^*[ModuleCat.{u + 1} R]
      (pullback.fst i (o k))^*[ModuleCat.{u + 1} R]
    have : IsIso ((pullback.fst i (o k))^*[ModuleCat.{u + 1} R].map
        (limit.post D (i)^*[ModuleCat.{u + 1} R]) ≫
        limit.post (D ⋙ (i)^*[ModuleCat.{u + 1} R])
          (pullback.fst i (o k))^*[ModuleCat.{u + 1} R]) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (limit.post (D ⋙ (i)^*[ModuleCat.{u + 1} R])
      (pullback.fst i (o k))^*[ModuleCat.{u + 1} R])
  have : IsIso (limit.post D (i)^*[ModuleCat.{u + 1} R]) :=
    isIso_of_forall_isIso_upperStar_map (fun k ↦ pullback.fst i (o k)) (fun z ↦ by
      obtain ⟨y, hy⟩ := 𝒰.covers (i.base z)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback z y hy.symm
      exact ⟨𝒰.idx (i.base z), w, hw⟩) _ hc
  exact preservesLimit_of_isIso_post _ _

end ProEtale

end AlgebraicGeometry
