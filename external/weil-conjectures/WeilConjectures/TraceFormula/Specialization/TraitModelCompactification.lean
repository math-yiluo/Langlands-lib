/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.RingTheory.LaurentSeries
public import WeilConjectures.Compactification.ExtensionOverOpen
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap

/-!

# Compactification of trait models over the base

Let `S = Spec k'⟦t⟧` be the trait. Its generic point is the open immersion
`Spec K ⟶ S` with `K = Frac k'⟦t⟧ = k'⟦t⟧[1/t]` (`AlgebraicGeometry.traitGenericSpec`), through
which the geometric generic point `Spec Ω ⟶ S` factors by a faithfully flat morphism.

Every trait model `M` of `X` over the base (`NearbyCyclesModel.IsTraitModelOfBase`) is an open
sub-model of a trait model over the base with proper total space, proper `X̄` and proper special
fibre `X̄'` (`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`). Construction:
let `X̄` be a Nagata compactification of `X` over `k` and `Z = X̄ ×_k S`; the morphism
`F = (e, q) : 𝒳 ⟶ Z` is an open immersion over the generic point of `S`, by fpqc descent
(Stacks 02L3) from the geometric generic fibre. A compactification of `F` which is an isomorphism
over the generic fibre `Z_K` (`AlgebraicGeometry.exists_isProper_isPullback_of_isOpenImmersion`)
is the total space of the required model; its geometric generic fibre is `X̄ ×_k Spec Ω`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

section TraitGeneric

variable (k' : Type u) [Field k']

/-- The field of fractions of `k'⟦t⟧` is its localization away from `t`. -/
instance isLocalization_away_X_fractionRing_powerSeries :
    IsLocalization.Away (PowerSeries.X : PowerSeries k') (FractionRing (PowerSeries k')) :=
  IsLocalization.isLocalization_of_algEquiv (M := Submonoid.powers PowerSeries.X)
    (FractionRing.algEquiv (PowerSeries k') (LaurentSeries k')).symm

/-- The generic point `Spec K ⟶ Spec k'⟦t⟧` of the trait, `K = Frac k'⟦t⟧`: an open immersion. -/
noncomputable def traitGenericSpec : Spec (.of (FractionRing (PowerSeries k'))) ⟶ trait k' :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k') (FractionRing (PowerSeries k'))))

instance : IsOpenImmersion (traitGenericSpec k') :=
  IsOpenImmersion.of_isLocalization (PowerSeries.X : PowerSeries k')

/-- The geometric generic point `Spec Ω ⟶ Spec K` over the generic point of the trait. -/
noncomputable def traitGenericPointToSpec :
    Spec (.of (traitGenericField k')) ⟶ Spec (.of (FractionRing (PowerSeries k'))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')))

@[reassoc]
lemma traitGenericPointToSpec_traitGenericSpec :
    traitGenericPointToSpec k' ≫ traitGenericSpec k' = traitGenericPoint k' := by
  rw [traitGenericPointToSpec, traitGenericSpec, traitGenericPoint, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The geometric generic point `Spec Ω ⟶ Spec K` is surjective, flat and quasi-compact. -/
lemma traitGenericPointToSpec_mem :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (traitGenericPointToSpec k') := by
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom
    (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')))).2
    (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)
  exact ⟨⟨h.2, h.1⟩, inferInstanceAs (QuasiCompact (Spec.map _))⟩

end TraitGeneric

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- **Compactification of trait models over the base**: a trait model `M` of `X` over the base
is an open sub-model of a trait model `M̄` over the base with proper total space and proper `X̄`,
`X̄'`, over open immersions `j : X ⟶ X̄` and `j' : X' ⟶ X̄'`, in the sense of
`NearbyCyclesModel.isIso_nearbyDualityMap_of_openSubmodel`. The geometric generic fibre of `M̄` is
all of `X̄ ×_k Spec Ω` (a pullback square). -/
theorem IsTraitModelOfBase.exists_isProper_openSubmodel {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfBase k q g) :
    ∃ (Xc : Over (Spec (.of k))) (_ : LocallyOfFiniteType Xc.hom) (_ : QuasiCompact Xc.hom)
      (_ : IsSeparated Xc.hom) (_ : IsProper (toPoint Xc).left) (Xc' : Over (Spec (.of k')))
      (_ : LocallyOfFiniteType Xc'.hom) (_ : QuasiCompact Xc'.hom) (_ : IsSeparated Xc'.hom)
      (_ : IsProper (toPoint Xc').left) (Mc : NearbyCyclesModel Xc.left Xc'.left)
      (qc : Mc.total ⟶ trait k') (gc : Mc.generic ⟶ Spec (.of (traitGenericField k')))
      (_ : Mc.IsTraitModelOfBase k qc gc)
      (_ : IsPullback Mc.ε gc Xc.hom (traitGenericPoint k' ≫ traitToBase k k'))
      (_ : IsProper qc) (j : X ⟶ Xc)
      (_ : IsOpenImmersion j.left) (j' : X' ⟶ Xc') (_ : IsOpenImmersion j'.left)
      (φ : M.Hom Mc j.left j'.left) (_ : IsOpenImmersion φ.total),
      IsPullback φ.generic M.j Mc.j φ.total ∧ q = φ.total ≫ qc ∧ g = φ.generic ≫ gc := by
  obtain ⟨e, he, heq⟩ := h.exists_comp_ε
  obtain ⟨u, hu, hu₁, hu₂⟩ := h.exists_openImmersion
  have hM := h.isTraitModelOver
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  -- the compactification `X̄` of `X` and `Z = X̄ ×_k S`
  let c₀ := NagataCompactification X.hom
  let tb := traitToBase k k'
  let z : pullback c₀.g tb ⟶ trait k' := pullback.snd _ _
  let F : M.total ⟶ pullback c₀.g tb :=
    pullback.lift (e ≫ c₀.i) q (by rw [Category.assoc, ← c₀.comm, heq])
  have hFz : F ≫ z = q := pullback.lift_snd _ _ _
  have hFfst : F ≫ pullback.fst c₀.g tb = e ≫ c₀.i := pullback.lift_fst _ _ _
  -- the generic points
  let ι := traitGenericSpec k'
  let γ' := traitGenericPointToSpec k'
  let γ := traitGenericPoint k'
  have hγ : γ' ≫ ι = γ := traitGenericPointToSpec_traitGenericSpec k'
  -- the generic fibre `V = Z_K` and `A' = 𝒳_K`
  let ιZ : pullback z ι ⟶ pullback c₀.g tb := pullback.fst z ι
  let a : pullback q ι ⟶ M.total := pullback.fst q ι
  let F' : pullback q ι ⟶ pullback z ι := pullback.lift (a ≫ F) (pullback.snd q ι)
    (by rw [Category.assoc, hFz, pullback.condition])
  have hF'snd : F' ≫ pullback.snd z ι = pullback.snd q ι := pullback.lift_snd _ _ _
  have hA : IsPullback a F' F ιZ := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback z ι)
    rw [hF'snd, hFz]
    exact IsPullback.of_hasPullback q ι
  -- the geometric generic fibre `Z_Ω`
  let toV : pullback z γ ⟶ pullback z ι :=
    pullback.lift (pullback.fst z γ) (pullback.snd z γ ≫ γ')
      (by rw [Category.assoc, hγ, pullback.condition])
  have hV : IsPullback toV (pullback.snd z γ) (pullback.snd z ι) γ' := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback z ι)
    rw [pullback.lift_fst, hγ]
    exact IsPullback.of_hasPullback z γ
  have hZΩ : IsPullback (pullback.fst z γ ≫ pullback.fst c₀.g tb) (pullback.snd z γ) c₀.g
      (γ ≫ tb) :=
    (IsPullback.of_hasPullback z γ).paste_horiz (IsPullback.of_hasPullback c₀.g tb)
  -- the morphism of geometric generic fibres
  let φgen : M.generic ⟶ pullback z γ :=
    pullback.lift (M.j ≫ F) g (by rw [Category.assoc, hFz, hM.isPullback_j.w])
  have hφgen_fst : φgen ≫ pullback.fst z γ = M.j ≫ F := pullback.lift_fst _ _ _
  have hφgen_snd : φgen ≫ pullback.snd z γ = g := pullback.lift_snd _ _ _
  have hgen : IsPullback φgen M.j (pullback.fst z γ) F := by
    refine IsPullback.of_right ?_ hφgen_fst (IsPullback.of_hasPullback z γ).flip
    rw [hφgen_snd, hFz]
    exact hM.isPullback_j.flip
  let snd' : M.generic ⟶ pullback q ι :=
    pullback.lift M.j (g ≫ γ') (by rw [Category.assoc, hγ, hM.isPullback_j.w])
  have hsnd'a : snd' ≫ a = M.j := pullback.lift_fst _ _ _
  have hP : IsPullback φgen snd' toV F' := by
    refine IsPullback.of_bot ?_ ?_ hA.flip
    · rw [hsnd'a, pullback.lift_fst]
      exact hgen
    · have htoV_fst : toV ≫ pullback.fst z ι = pullback.fst z γ := pullback.lift_fst _ _ _
      have htoV_snd : toV ≫ pullback.snd z ι = pullback.snd z γ ≫ γ' := pullback.lift_snd _ _ _
      have hF'fst : F' ≫ pullback.fst z ι = a ≫ F := pullback.lift_fst _ _ _
      have hsnd'snd : snd' ≫ pullback.snd q ι = g ≫ γ' := pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, htoV_fst, hF'fst, hφgen_fst, ← Category.assoc,
          hsnd'a]
      · rw [Category.assoc, Category.assoc, htoV_snd, hF'snd, hsnd'snd, ← Category.assoc,
          hφgen_snd]
  -- `φgen` is an open immersion: it is `u` followed by `X_Ω ⟶ X̄_Ω`
  have : IsOpenImmersion φgen := by
    have hcomp : φgen ≫ hZΩ.isoPullback.hom = u ≫ pullback.map X.hom (γ ≫ tb) c₀.g (γ ≫ tb)
        c₀.i (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact c₀.comm) (by simp) := by
      apply pullback.hom_ext
      · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, hφgen_fst,
          Category.assoc, hFfst, ← Category.assoc, he, Category.assoc, pullback.lift_fst,
          ← Category.assoc, hu₁]
      · rw [Category.assoc, IsPullback.isoPullback_hom_snd, hφgen_snd, Category.assoc,
          pullback.lift_snd, Category.comp_id, hu₂]
    have : IsOpenImmersion (φgen ≫ hZΩ.isoPullback.hom) := by
      rw [hcomp]
      infer_instance
    exact IsOpenImmersion.of_comp φgen hZΩ.isoPullback.hom
  -- descent: `F'` is an open immersion
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) toV :=
    MorphismProperty.of_isPullback hV.flip (traitGenericPointToSpec_mem k')
  have : IsOpenImmersion F' :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion) hP hQ
      inferInstance
  -- the compactification over `Z`, an isomorphism over `Z_K`
  have : QuasiCompact F := by
    have : QuasiCompact (F ≫ z) := by rw [hFz]; infer_instance
    exact QuasiCompact.of_comp F z
  have : IsSeparated F := by
    have : IsSeparated (F ≫ z) := by rw [hFz]; infer_instance
    exact IsSeparated.of_comp F z
  have : LocallyOfFiniteType F := by
    have : LocallyOfFiniteType (F ≫ z) := by rw [hFz]; infer_instance
    exact locallyOfFiniteType_of_comp F z
  have := quasiSeparatedSpace_of_quasiSeparated z
  obtain ⟨B, c, p, s, hc, hp, hcp, has, hps⟩ :=
    exists_isProper_isPullback_of_isOpenImmersion (F := F) (ι := ιZ) hA
  -- the compactified model
  let qc : B ⟶ trait k' := p ≫ z
  have hqc : q = c ≫ qc := by rw [← hFz, ← hcp, Category.assoc]
  let Xc : Over (Spec (.of k)) := Over.mk c₀.g
  let Xc' : Over (Spec (.of k')) := Over.mk (pullback.snd qc (traitClosedPoint k'))
  let Mc : NearbyCyclesModel Xc.left Xc'.left :=
    { total := B
      generic := pullback z γ
      j := toV ≫ s
      i := pullback.fst qc (traitClosedPoint k')
      ε := pullback.fst z γ ≫ pullback.fst c₀.g tb }
  have hMcj : IsPullback (toV ≫ s) (pullback.snd z γ) qc γ := by
    have h₂ : IsPullback s (pullback.snd z ι) qc ι := by
      simpa using hps.paste_vert (IsPullback.of_hasPullback z ι)
    have h₃ := hV.paste_horiz h₂
    rwa [hγ] at h₃
  have hMc : Mc.IsTraitModelOfBase k qc (pullback.snd z γ) := by
    refine IsTraitModelOfBase.of_isPullback ⟨inferInstance, inferInstance, inferInstance, hMcj,
      IsPullback.of_hasPullback _ _⟩ ⟨p ≫ pullback.fst c₀.g tb, ?_, ?_⟩ hZΩ
    · change (toV ≫ s) ≫ p ≫ pullback.fst c₀.g tb = pullback.fst z γ ≫ pullback.fst c₀.g tb
      rw [Category.assoc, reassoc_of% hps.w, pullback.lift_fst_assoc]
    · change (p ≫ pullback.fst c₀.g tb) ≫ c₀.g = (p ≫ z) ≫ tb
      rw [Category.assoc, pullback.condition, Category.assoc]
  -- the open immersions `j` and `j'`
  let j : X ⟶ Xc := Over.homMk c₀.i c₀.comm.symm
  let j'l : X'.left ⟶ Xc'.left := pullback.lift (M.i ≫ c) X'.hom
    (by rw [Category.assoc, ← hqc, hM.isPullback_i.w])
  let j' : X' ⟶ Xc' := Over.homMk j'l (pullback.lift_snd _ _ _)
  have hj' : IsPullback j'l M.i Mc.i c := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback qc (traitClosedPoint k')).flip
    rw [pullback.lift_snd, ← hqc]
    exact hM.isPullback_i.flip
  have : IsOpenImmersion j'l := MorphismProperty.of_isPullback hj'.flip hc
  -- the morphism of models
  have hcomm_j : φgen ≫ Mc.j = M.j ≫ c := by
    change φgen ≫ toV ≫ s = M.j ≫ c
    rw [reassoc_of% hP.w, ← has, ← Category.assoc, hsnd'a]
  let φ : M.Hom Mc j.left j'.left :=
    { total := c
      generic := φgen
      comm_j := hcomm_j
      comm_i := pullback.lift_fst _ _ _
      comm_ε := by
        change φgen ≫ pullback.fst z γ ≫ pullback.fst c₀.g tb = M.ε ≫ c₀.i
        rw [reassoc_of% hφgen_fst, hFfst, ← Category.assoc, he] }
  refine ⟨Xc, inferInstanceAs (LocallyOfFiniteType c₀.g), inferInstanceAs (QuasiCompact c₀.g),
    inferInstanceAs (IsSeparated c₀.g),
    by simp only [toPoint_left]; exact inferInstanceAs (IsProper c₀.g), Xc',
    inferInstanceAs (LocallyOfFiniteType (pullback.snd qc (traitClosedPoint k'))),
    inferInstanceAs (QuasiCompact (pullback.snd qc (traitClosedPoint k'))),
    inferInstanceAs (IsSeparated (pullback.snd qc (traitClosedPoint k'))),
    by simp only [toPoint_left]
       exact inferInstanceAs (IsProper (pullback.snd qc (traitClosedPoint k'))),
    Mc, qc,
    pullback.snd z γ, hMc, hZΩ, inferInstanceAs (IsProper (p ≫ z)), j,
    inferInstanceAs (IsOpenImmersion c₀.i), j', inferInstanceAs (IsOpenImmersion j'l), φ, hc,
    ?_, hqc, hφgen_snd.symm⟩
  refine IsPullback.of_right ?_ hcomm_j hMcj.flip
  rw [hφgen_snd]
  rw [← hqc]
  exact hM.isPullback_j.flip

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
