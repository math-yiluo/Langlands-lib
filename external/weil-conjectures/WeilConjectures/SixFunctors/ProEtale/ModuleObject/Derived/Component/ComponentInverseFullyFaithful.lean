/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.AlgebraicGeometry.Affine.AffineComponentSiteProjection
import WeilConjectures.AlgebraicGeometry.ZetaWeil.StalkIsomorphismLifting
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleCoverSection
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology

set_option linter.privateModule false

/-! # Full faithfulness of component inverse image on abelian sheaves
Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.2).
(blueprint: lem-zl-component-inverse-fully-faithful).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite Topology
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem pullback_wcontractible (R : Type u) [CommRing R]
    [IsWContractibleRing R] (E : Profinite.{u}) [ExtremallyDisconnected E]
    (i : C(E, ConnectedComponents (PrimeSpectrum R))) :
    IsWContractibleRing (WContractification.PullbackProfinite R E i) := by
  let D := WContractification.PullbackProfinite R E i
  have pb := WContractification.PullbackProfinite.isPullback R E i
  let : WLocalSpace (PrimeSpectrum D) :=
    ConnectedComponents.wlocalSpace_of_isPullback pb
  let : IsWLocalRing D := ⟨inferInstance⟩
  have hbos : Algebra.BijectiveOnStalks R D :=
    inferInstance
  let : IsWStrictlyLocalRing D := by
    refine ⟨fun m hm ↦ ?_⟩
    let : m.IsPrime := hm.isPrime
    let y : PrimeSpectrum D := ⟨m, inferInstance⟩
    have hy : y ∈ closedPoints (PrimeSpectrum D) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hm
    have hpre :=
      ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback pb
    have hxc : WContractification.PullbackProfinite.projSpec R E i y ∈
        closedPoints (PrimeSpectrum R) := by
      rw [← hpre] at hy
      exact hy
    let : (m.comap (algebraMap R D)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hxc
    let := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
      (R := R) (m.comap (algebraMap R D))
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (RingEquiv.ofBijective _ (hbos.bijective_localRingHom m))
  have hED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) :=
    extremallyDisconnected_of_homeo
      (ConnectedComponents.isHomeomorph_lift_of_isPullback pb).homeomorph.symm
  exact { extremallyDisconnected_connectedComponents := hED }

private theorem iso_of_stalks_homeo {X Y T : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T)
    (hf : ∀ x, IsIso (f.stalkMap x)) (hg : ∀ y, IsIso (g.stalkMap y))
    (h : X ≃ₜ Y) (hh : ∀ x, g (h x) = f x) :
    ∃ e : X ≅ Y, e.hom ≫ g = f ∧ ∀ x, e.hom x = h x := by
  let a : X.toTopCat ⟶ Y.toTopCat := TopCat.ofHom ⟨h, h.continuous⟩
  let b : Y.toTopCat ⟶ X.toTopCat := TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  obtain ⟨m, hm, hmu⟩ := Scheme.existsUnique_lift_of_stalkMap_isIso g hg f a
    (by ext x; exact hh x)
  obtain ⟨n, hn, hnu⟩ := Scheme.existsUnique_lift_of_stalkMap_isIso f hf g b
    (by ext y; exact (hh (h.symm y)).symm.trans (congrArg g (h.apply_symm_apply y)))
  have hmn : m ≫ n = 𝟙 X := by
    apply (Scheme.existsUnique_lift_of_stalkMap_isIso f hf f (𝟙 X.toTopCat)
      (by simp)).unique
    · constructor
      · rw [Scheme.Hom.comp_base, hm.1, hn.1]
        ext x
        exact h.symm_apply_apply x
      · rw [Category.assoc, hn.2, hm.2]
    · exact ⟨rfl, Category.id_comp _⟩
  have hnm : n ≫ m = 𝟙 Y := by
    apply (Scheme.existsUnique_lift_of_stalkMap_isIso g hg g (𝟙 Y.toTopCat)
      (by simp)).unique
    · constructor
      · rw [Scheme.Hom.comp_base, hn.1, hm.1]
        ext y
        exact h.apply_symm_apply y
      · rw [Category.assoc, hm.2, hn.2]
    · exact ⟨rfl, Category.id_comp _⟩
  exact ⟨⟨m, n, hmn, hnm⟩, hm.2, fun x ↦ ConcreteCategory.congr_hom hm.1 x⟩

private theorem test_spectrum (T : Scheme.{u}) [IsAffine T]
    [IsWContractibleRing Γ(T, ⊤)] (W : T.ProEt)
    (E : Over (affineComponentSpace T)) [ExtremallyDisconnected E.left]
    (hstalk : ∀ x, IsIso (W.hom.stalkMap x))
    (hW : ∃ h : W.left ≃ₜ
        {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
      ∀ x, (h x).val.1 = W.hom x) :
    ∃ D : CommRingCat.{u}, IsWContractibleRing D ∧ Nonempty (W.left ≅ Spec D) := by
  classical
  let R := Γ(T, ⊤)
  let e := Scheme.homeoOfIso T.isoSpec
  let i : C(E.left, ConnectedComponents (PrimeSpectrum R)) :=
    ⟨fun x ↦ T.isoSpec.hom.continuous.connectedComponentsMap (E.hom x),
      T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
        E.hom.hom.hom.continuous⟩
  let D := WContractification.PullbackProfinite R E.left i
  let : IsWContractibleRing D := pullback_wcontractible R E.left i
  let f : Spec (.of D) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap R D)) ≫ T.isoSpec.inv
  let hD : Spec (.of D) ≃ₜ
      {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2} :=
    (WContractification.PullbackProfinite.fiberHomeo R E.left i).trans
      { toFun := fun p ↦ ⟨(e.symm p.1.2, p.1.1), by
          change ConnectedComponents.mk (e.symm p.1.2) = E.hom p.1.1
          have hp := p.2
          obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.hom p.1.1)
          change T.isoSpec.hom.continuous.connectedComponentsMap (E.hom p.1.1) = _ at hp
          rw [← hx, Continuous.connectedComponentsMap_mk] at hp
          change ConnectedComponents.mk (e x) = ConnectedComponents.mk p.1.2 at hp
          have hi := congrArg e.symm.continuous.connectedComponentsMap hp
          simpa only [Continuous.connectedComponentsMap_mk, e.symm_apply_apply, hx]
            using hi.symm⟩
        invFun := fun p ↦ ⟨(p.1.2, e p.1.1), by
          change T.isoSpec.hom.continuous.connectedComponentsMap (E.hom p.1.2) = _
          rw [← p.2, Continuous.connectedComponentsMap_mk]
          rfl⟩
        left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (e.apply_symm_apply _))
        right_inv := fun p ↦ Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact (e.symm.continuous.comp
            (continuous_snd.comp continuous_subtype_val)).prodMk
              (continuous_fst.comp continuous_subtype_val)
        continuous_invFun := by
          apply Continuous.subtype_mk
          exact (continuous_snd.comp continuous_subtype_val).prodMk
            (e.continuous.comp (continuous_fst.comp continuous_subtype_val)) }
  have hf (x : Spec (.of D)) : IsIso (f.stalkMap x) := by
    let φ : CommRingCat.of R ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap R D)
    have hb : IsIso (CommRingCat.ofHom (Localization.localRingHom
        (PrimeSpectrum.comap φ.hom x).asIdeal x.asIdeal φ.hom rfl)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (Algebra.BijectiveOnStalks.bijective_localRingHom (R := R) x.asIdeal)
    have hi : IsIso ((Spec.map φ).stalkMap x) := by
      rw [← Scheme.localRingHom_comp_stalkIso]
      infer_instance
    dsimp only [f]
    rw [Scheme.Hom.stalkMap_comp]
    infer_instance
  obtain ⟨h, ht⟩ := hW
  obtain ⟨j, _, _⟩ := iso_of_stalks_homeo f W.hom hf hstalk (hD.trans h.symm) (by
    intro x
    change W.hom (h.symm (hD x)) = f x
    rw [← ht, h.apply_symm_apply]
    change T.isoSpec.inv
        (WContractification.PullbackProfinite.fiberHomeo R E.left i x).1.2 = _
    rw [WContractification.PullbackProfinite.snd_fiberHomeo]
    rfl)
  exact ⟨.of D, inferInstance, ⟨j.symm⟩⟩

private theorem test_hom_ext (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E, C((F.obj E).left, E.left))
    (hp : ∀ E x, E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x))
    (hmap : ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
      (∀ w, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
      ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
        ∀ w, p E (m.left w) = g w)
    {W : T.ProEt} {E : Over (affineComponentSpace T)} (a b : W ⟶ F.obj E)
    (hab : ∀ w, p E (a.left w) = p E (b.left w)) : a = b := by
  apply (Scheme.ProEt.forget T).map_injective
  let g : C(W.left, E.left) := (p E).comp ⟨b.left, b.left.continuous⟩
  have hg (w) : E.hom (g w) = ConnectedComponents.mk (W.hom w) :=
    (hp E _).trans (congrArg ConnectedComponents.mk
      (congrArg (fun l ↦ l w) b.w))
  exact (hmap ((Scheme.ProEt.forget T).obj W) E g hg).unique hab (fun _ ↦ rfl)

private theorem tests_iso (T : Scheme.{u}) [IsAffine T]
    (U : Over (affineComponentSpace T) ⥤ T.ProEt)
    (r : ∀ E, C((U.obj E).left, E.left))
    (hU : ∀ E, (∀ x, IsIso ((U.obj E).hom.stalkMap x)) ∧
      ∃ h : (U.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (U.obj E).hom x) ∧ (∀ x, (h x).val.2 = r E x))
    (hrnat : ∀ E E' (a : E ⟶ E') x,
      r E' ((U.map a).left x) = a.left (r E x)) :
    Nonempty (componentTests T ≅ U) := by
  classical
  let F := componentTests T
  obtain ⟨p, hp, hpnat, hmap⟩ :=
    (Classical.choose_spec (component_relative_profinite_site T)).2.1
  obtain ⟨hr, hmapU⟩ := component_mapping_property T U r hU
  let m (E : Over (affineComponentSpace T)) :=
    (hmapU ((Scheme.ProEt.forget T).obj (F.obj E)) E (p E) (hp E)).choose
  have hm (E) (x) : r E ((m E).left x) = p E x :=
    (hmapU ((Scheme.ProEt.forget T).obj (F.obj E)) E (p E) (hp E)).choose_spec.1 x
  let n (E : Over (affineComponentSpace T)) :=
    (hmap ((Scheme.ProEt.forget T).obj (U.obj E)) E (r E) (hr E)).choose
  have hn (E) (x) : p E ((n E).left x) = r E x :=
    (hmap ((Scheme.ProEt.forget T).obj (U.obj E)) E (r E) (hr E)).choose_spec.1 x
  let m' (E) : F.obj E ⟶ U.obj E := MorphismProperty.Over.homMk (m E).left (m E).w
  let n' (E) : U.obj E ⟶ F.obj E := MorphismProperty.Over.homMk (n E).left (n E).w
  have hm' (E) x : r E ((m' E).left x) = p E x := hm E x
  have hn' (E) x : p E ((n' E).left x) = r E x := hn E x
  refine ⟨NatIso.ofComponents (fun E ↦ ⟨m' E, n' E, ?_, ?_⟩) ?_⟩
  · apply test_hom_ext T F p hp hmap
    intro x
    change p E ((n' E).left ((m' E).left x)) = p E x
    rw [hn', hm']
  · apply test_hom_ext T U r hr hmapU
    intro x
    change r E ((m' E).left ((n' E).left x)) = r E x
    rw [hm', hn']
  · intro E E' a
    apply test_hom_ext T U r hr hmapU
    intro x
    change r E' ((m' E').left ((F.map a).left x)) =
      r E' ((U.map a).left ((m' E).left x))
    rw [hm', hrnat, hm']
    exact hpnat E E' a x

private theorem split_covers {T : Scheme.{u}} (W : Scheme.ProEt.Qcqs T)
    (D : CommRingCat.{u}) [IsWContractibleRing D] (e : W.obj.left ≅ Spec D) :
    Scheme.ProEt.HasSplitFiniteQcqsCovers W := by
  intro n V a hc
  have hc' : Presieve.ofArrows (fun i ↦ (V i).obj.left) (fun i ↦ (a i).left) ∈
      Scheme.proetalePrecoverage W.obj.left := by
    have h := Scheme.ProEt.mem_precoverage_iff.mp hc
    rw [Presieve.map_ofArrows] at h
    exact h
  let I := ULift.{u} (Fin n)
  let cov : W.obj.left.Cover Scheme.proetalePrecoverage :=
    { I₀ := I
      X := fun i ↦ (V i.down).obj.left
      f := fun i ↦ (a i.down).left
      mem₀ := by
        change Presieve.ofArrows (fun i : I ↦ (V i.down).obj.left)
          (fun i ↦ (a i.down).left) ∈ Scheme.proetalePrecoverage W.obj.left
        have hh := Presieve.ofArrows_comp_eq_of_surjective (fun i ↦ (a i).left)
          (a := fun i : I ↦ i.down) (fun i ↦ ⟨⟨i⟩, rfl⟩)
        exact hh.symm ▸ hc' }
  let cov' := cov.pushforward e.hom (Precoverage.mem_coverings_of_isIso e.hom)
  have hsplit (B : Type u) [CommRing B] [Algebra D B]
      (hff : Module.FaithfullyFlat D B) (hwe : Algebra.WeaklyEtale D B) :
      ∃ r : B →+* D, r.comp (algebraMap D B) = RingHom.id D := by
    obtain ⟨C, _, g, _, hgff, hge⟩ :=
      (RingHom.weaklyEtale_algebraMap_iff.mpr hwe).exists_indEtale_comp
    algebraize [g.comp (algebraMap D B)]
    have : Algebra.IndEtale D C := by rwa [← RingHom.IndEtale.algebraMap_iff]
    have : Module.FaithfullyFlat D C := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      exact RingHom.FaithfullyFlat.stableUnderComposition _ _
        (RingHom.faithfullyFlat_algebraMap_iff.mpr hff) hgff
    obtain ⟨r, hr⟩ := IsWContractibleRing.exists_retraction D C
    exact ⟨r.comp g, hr⟩
  obtain ⟨σ, hσ⟩ := exists_section_proetaleCover_of_ring_retractions D hsplit I
    (fun i ↦ (V i.down).obj.left) (fun i ↦ (a i.down).left ≫ e.hom) cov'.mem₀
  let k : (∐ fun i : I ↦ (V i.down).obj.left) ⟶ ∐ fun i ↦ (V i).obj.left :=
    Sigma.desc (fun i ↦ Sigma.ι (fun j ↦ (V j).obj.left) i.down)
  have hk : k ≫ Sigma.desc (fun i ↦ (a i).left) ≫ e.hom =
      Sigma.desc (fun i : I ↦ (a i.down).left ≫ e.hom) := by
    apply Sigma.hom_ext
    intro i
    simp only [k, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  refine ⟨e.hom ≫ σ ≫ k, ?_⟩
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Category.id_comp, hk]
  exact (congrArg (fun l ↦ e.hom ≫ l) hσ).trans (Category.comp_id _)

private theorem stonean_cover_mem {S : Profinite.{u}} {E : Over S} (R : Sieve E)
    (D : Profinite.{u}) (a : D ⟶ E.left) [EffectiveEpi a]
    (ha : R (Over.homMk a rfl : Over.mk (a ≫ E.hom) ⟶ E)) :
    R ∈ ((coherentTopology Profinite.{u}).over S) E := by
  rw [GrothendieckTopology.mem_over_iff]
  apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  refine ⟨Unit, inferInstance, (fun _ ↦ D), (fun _ ↦ a), ?_, fun _ ↦ ?_⟩
  · exact (effectiveEpi_iff_effectiveEpiFamily a).mp inferInstance
  · rw [Sieve.overEquiv_iff]
    exact ha

private theorem iso_of_stonean {S : Profinite.{u}}
    {F G : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1}} (f : F ⟶ G)
    (hf : ∀ E : Over S, ExtremallyDisconnected E.left → IsIso (f.hom.app (op E))) :
    IsIso f := by
  let J := (coherentTopology Profinite.{u}).over S
  have hcover (E : Over S) (R : Sieve E)
      (hR : ∀ (D : Over S), ExtremallyDisconnected D.left → ∀ a : D ⟶ E, R a) :
      R ∈ J E := by
    let D := Stonean.toProfinite.obj E.left.presentation
    let a := Profinite.presentation.π E.left
    let : ExtremallyDisconnected D :=
      inferInstanceAs (ExtremallyDisconnected E.left.presentation)
    have : EffectiveEpi a := ((Profinite.effectiveEpi_tfae a).out 1 2).mpr (inferInstance : Epi a)
    exact stonean_cover_mem R D a (hR (Over.mk (a ≫ E.hom))
      (show ExtremallyDisconnected D from inferInstance)
      (Over.homMk a rfl))
  have hsurj : Presheaf.IsLocallySurjective J f.hom := by
    constructor
    intro E s
    apply hcover
    intro D hD a
    have : IsIso (f.hom.app (op D)) := hf D hD
    refine ⟨inv (f.hom.app (op D)) (G.obj.map a.op s), ?_⟩
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (f.hom.app (op D))) _
  have hinj : Presheaf.IsLocallyInjective J f.hom := by
    constructor
    intro E x y hxy
    apply hcover
    intro D hD a
    have : IsIso (f.hom.app (op D)) := hf D hD
    apply ((ConcreteCategory.isIso_iff_bijective (f.hom.app (op D))).mp
      inferInstance).injective
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  exact (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨hinj, hsurj⟩

end AlgebraicGeometry.ProEtale.CondensedRing
