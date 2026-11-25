/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedCoverExtension
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Trivialization
public import WeilConjectures.WeilSheaf.LisseLocus

/-!
# Nil-invariance of lissity

Let `i : Z ⟶ Y` be a surjective closed immersion of schemes, for instance the inclusion of the
reduced subscheme. A sheaf `G` of `ℚ̄_ℓ`-modules on `Y_proét` is lisse as soon as `i^* G` is
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_adicUpperStar_of_surjective`). This is the part
of the topological invariance of the pro-étale site (Stacks 09BK) needed for lissity.

Lissity being Zariski local, we may assume `Y = Spec B` affine and `Z = Spec (B ⧸ J)` with `J`
contained in every prime ideal. A trivialising cover of `i^* G` is refined by finitely many
`Spec C_a` with `C_a` ind-étale over `B ⧸ J`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_indEtale_cover`). Their closed lifts
`Spec H_B(C_a)` (`Algebra.ClosedLift`), together with basic opens `D(f)`, `f ∈ J`, which are
empty, form a pro-étale cover of `Y`
(`AlgebraicGeometry.exists_ofArrows_closedLiftCover_mem_proetalePrecoverage`). The morphism
`Spec C_a ⟶ Spec H_B(C_a)` is a surjective closed immersion, being a base change of `i`,
and the pullback along a surjective closed immersion `s` reflects isomorphism classes, the
unit `M ⟶ s_* s^* M` being invertible
(`AlgebraicGeometry.ProEtale.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_surjective`).
Hence the trivialisation of `i^* G` on `Spec C_a` comes from one of `G` on `Spec H_B(C_a)`.

As a consequence, lissity near generic points of constructible sheaves holds without
reducedness (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.exists_opens_isAdicLisseSheaf'`).

## Main statements

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_adicUpperStar_of_surjective`
- `AlgebraicGeometry.ProEtale.isoOfAdicUpperStarIso`
- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.upperStar_opensι_of_subset_range'`
- `AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.exists_opens_isAdicLisseSheaf'`
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The closed lift `H_B(C)` of an ind-étale `B ⧸ J`-algebra `C` reduces to `C`: the square of
rings `B ⟶ B ⧸ J ⟶ C`, `B ⟶ H_B(C) ⟶ C` is a pushout
(`Algebra.ClosedLift.bijective_reduction`). -/
theorem Algebra.ClosedLift.isPushout (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (J : Ideal B) [Algebra (B ⧸ J) C] [IsScalarTower B (B ⧸ J) C] [Algebra.IndEtale (B ⧸ J) C] :
    CategoryTheory.IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (algebraMap B (Algebra.ClosedLift B C)))
      (CommRingCat.ofHom (algebraMap (B ⧸ J) C))
      (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom B C).toRingHom) := by
  let e := (RingEquiv.ofBijective (Algebra.ClosedLift.reduction B C J)
    (Algebra.ClosedLift.bijective_reduction B C J)).toCommRingCatIso
  refine (CommRingCat.isPushout_quotient
    (CommRingCat.ofHom (algebraMap B (Algebra.ClosedLift B C))) J).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Algebra.ClosedLift.toAlgHom B C
      (algebraMap B (Algebra.ClosedLift B C) a) = algebraMap (B ⧸ J) C _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B (B ⧸ J) C]
    rfl
  · rfl

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section SurjectiveClosedImmersion

variable {T L : Scheme.{u}} (s : T ⟶ L) [IsClosedImmersion s] [Surjective s]

/-- Along a surjective closed immersion `s`, the unit `M ⟶ s_* s^* M` is an isomorphism for
every `ℓ`-adic sheaf `M`: the open complement of `s` is empty
(`AlgebraicGeometry.ProEtale.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl`). -/
theorem isIso_adicUpperStarLowerStarAdjunction_unit_app_of_surjective (M : AdicSheaf l L) :
    IsIso ((adicUpperStarLowerStarAdjunction l s).unit.app M) := by
  have : IsEmpty (⊥ : L.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have : QuasiCompact (⊥ : L.Opens).ι := ⟨fun _ _ _ ↦ Set.subsingleton_of_subsingleton.isCompact⟩
  have hij : IsCompl (Set.range s.base) (Set.range (⊥ : L.Opens).ι.base) := by
    rw [Set.range_eq_univ.2 s.surjective, Scheme.Opens.range_ι]
    exact isCompl_top_bot
  exact isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl s (⊥ : L.Opens).ι hij M
    (isZero_adicSheaf_of_isEmpty l _)

/-- Pullback along a surjective closed immersion `s` reflects isomorphism classes: an
isomorphism `s^* M ≅ s^* N` induces `M ≅ s_* s^* M ≅ s_* s^* N ≅ N`. -/
noncomputable def isoOfAdicUpperStarIso {M N : AdicSheaf l L}
    (e : (s)^*ᵃ[l].obj M ≅ (s)^*ᵃ[l].obj N) : M ≅ N :=
  have := isIso_adicUpperStarLowerStarAdjunction_unit_app_of_surjective s M
  have := isIso_adicUpperStarLowerStarAdjunction_unit_app_of_surjective s N
  asIso ((adicUpperStarLowerStarAdjunction l s).unit.app M) ≪≫ (s)_*ᵃ[l].mapIso e ≪≫
    (asIso ((adicUpperStarLowerStarAdjunction l s).unit.app N)).symm

end SurjectiveClosedImmersion

/-- If `g^* F` is lisse and `f ≫ g = k`, then `k^* F` is lisse. -/
theorem IsAdicLisseSheaf.upperStar_of_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (h : f ≫ g = k) {F : AdicSheaf l Z} (hF : IsAdicLisseSheaf ((g)^*ᵃ[l].obj F)) :
    IsAdicLisseSheaf ((k)^*ᵃ[l].obj F) :=
  (hF.upperStar f).of_iso (((adicUpperStarComp l f g).app F).symm ≪≫
    (adicUpperStarCongr l h).app F)

/-- If `k^* F` is lisse and `f ≫ g = k`, then `f^* g^* F` is lisse. -/
theorem IsAdicLisseSheaf.upperStar_upperStar_of_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y}
    {g : Y ⟶ Z} {k : X ⟶ Z} (h : f ≫ g = k) {F : AdicSheaf l Z}
    (hF : IsAdicLisseSheaf ((k)^*ᵃ[l].obj F)) :
    IsAdicLisseSheaf ((f)^*ᵃ[l].obj ((g)^*ᵃ[l].obj F)) :=
  hF.of_iso ((adicUpperStarCongr l h.symm).app F ≪≫ (adicUpperStarComp l f g).app F)

/-- A sheaf whose pullback along an isomorphism is lisse is lisse. -/
theorem IsAdicLisseSheaf.of_upperStar_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {F : AdicSheaf l Y} (hF : IsAdicLisseSheaf ((f)^*ᵃ[l].obj F)) : IsAdicLisseSheaf F :=
  (hF.upperStar_of_comp (IsIso.inv_hom_id f)).of_iso ((adicUpperStarId l Y).app F)

/-- **Ind-étale affine trivialising covers.** A lisse sheaf on an affine scheme `Spec R` is
trivialised on finitely many jointly surjective `Spec T_a ⟶ Spec R` with `T_a` ind-étale over
`R`: refine a trivialising cover by finitely many affine opens of its members, and apply Stacks
097Z (`RingHom.WeaklyEtale.exists_indEtale_comp`) to each of them. -/
theorem IsAdicLisseSheaf.exists_indEtale_cover {R : CommRingCat.{u}}
    {F : AdicSheaf l (Spec R)} (hF : IsAdicLisseSheaf F) :
    ∃ (ι : Type u) (_ : Finite ι) (T : ι → CommRingCat.{u}) (φ : ∀ a, R ⟶ T a),
      (∀ a, (φ a).hom.IndEtale) ∧ (∀ x : Spec R, ∃ a, x ∈ Set.range (Spec.map (φ a))) ∧
      ∀ a, ∃ n : ℕ, Nonempty ((Spec.map (φ a))^*ᵃ[l].obj F ≅
        ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (T a))) := by
  classical
  obtain ⟨Rc, hR, hRF⟩ := hF
  obtain ⟨ι, V, f, rfl⟩ := Rc.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRF (f i) (.mk i)
  let E : PreZeroHypercover (Spec R) := ⟨ι, V, f⟩
  have : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.1
    ((show Scheme.proetalePrecoverage ≤ Scheme.qcPrecoverage from inf_le_left) _ hR)
  obtain ⟨N, a, W, hW, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) isCompact_univ
  -- Stacks 097Z on each affine piece
  have hpiece (s : Fin N) : ∃ (T : CommRingCat.{u}) (φ : R ⟶ T)
      (g : Spec T ⟶ (W s).toScheme), φ.hom.IndEtale ∧ Surjective g ∧
      Spec.map φ = g ≫ (W s).ι ≫ f (a s) := by
    have : IsAffine (W s).toScheme := hW s
    set Y := (W s).toScheme
    obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : R ⟶ Γ(Y, ⊤), Spec.map φ₀ = Y.isoSpec.inv ≫ (W s).ι ≫ f (a s) :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    have : WeaklyEtale (Spec.map φ₀) := by
      rw [hφ₀]
      infer_instance
    obtain ⟨T, _, g, -, hg, hgφ⟩ := ((WeaklyEtale.Spec_iff φ₀).1 ‹_›).exists_indEtale_comp
    have := ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom g)).2 hg).2
    refine ⟨.of T, φ₀ ≫ CommRingCat.ofHom g, Spec.map (CommRingCat.ofHom g) ≫ Y.isoSpec.inv,
      hgφ, inferInstance, ?_⟩
    rw [Spec.map_comp, hφ₀, Category.assoc]
  choose T φ g hφ hg hφg using hpiece
  refine ⟨ULift.{u} (Fin N), inferInstance, fun s ↦ T s.down, fun s ↦ φ s.down,
    fun s ↦ hφ s.down, fun x ↦ ?_, fun s ↦ ⟨n (a s.down), ⟨(adicUpperStarCongr l
      (hφg s.down)).app F ≪≫ (adicUpperStarCongr l (Category.assoc _ _ _).symm).app F ≪≫
      AdicSheaf.trivPull (f (a s.down)) (e (a s.down)).some _⟩⟩⟩
  have : x ∈ ⋃ i, E.f (a i) '' (W i : Set _) := by rw [hcov]; trivial
  obtain ⟨i, w, hw, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using this
  obtain ⟨t, ht⟩ := (g i).surjective ⟨w, hw⟩
  refine ⟨⟨i⟩, t, ?_⟩
  change (Spec.map (φ i)) t = _
  rw [hφg i, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht]
  rfl

/-- **Nil-invariance of lissity, affine case.** Let `J` be an ideal of `B` contained in every
prime ideal. If the pullback of `G` to `Spec (B ⧸ J)` is lisse, then `G` is lisse. -/
theorem IsAdicLisseSheaf.of_adicUpperStar_specMap_quotientMk {B : Type u} [CommRing B]
    (J : Ideal B) (hJ : ∀ p : PrimeSpectrum B, J ≤ p.asIdeal) {G : AdicSheaf l (Spec (.of B))}
    (hG : IsAdicLisseSheaf
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))^*ᵃ[l].obj G)) :
    IsAdicLisseSheaf G := by
  classical
  set p := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  obtain ⟨ι, _, T, φ, hφ, hsurj, htriv⟩ := hG.exists_indEtale_cover
  let (a : ι) : Algebra (B ⧸ J) (T a) := (φ a).hom.toAlgebra
  let (a : ι) : Algebra B (T a) := ((φ a).hom.comp (Ideal.Quotient.mk J)).toAlgebra
  have (a : ι) : IsScalarTower B (B ⧸ J) (T a) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have (a : ι) : Algebra.IndEtale (B ⧸ J) (T a) := hφ a
  have hJc : IsCompact (PrimeSpectrum.zeroLocus (J : Set B))ᶜ := by
    convert isCompact_empty
    ext q
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact hJ q
  obtain ⟨κ, _, f, hfJ, -, hcov, -, -⟩ :=
    exists_ofArrows_closedLiftCover_mem_proetalePrecoverage J (fun a ↦ T a) hJc
      (fun q ↦ by obtain ⟨a, x, hx⟩ := hsurj q; exact ⟨a, x, hx⟩)
  refine ⟨_, hcov, ?_⟩
  rintro _ _ ⟨k⟩
  rcases k with a | b
  · -- the lift `Spec H_B(T a)` reduces to `Spec (T a)`, on which `G` is trivial
    obtain ⟨n, ⟨e⟩⟩ := htriv a
    let H := Algebra.ClosedLift B (T a)
    let s := Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom B (T a)).toRingHom)
    have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (Algebra.ClosedLift.isPushout B (T a) J)
    have : IsClosedImmersion s := IsClosedImmersion.spec_of_surjective _
      (Algebra.ClosedLift.surjective_toAlgHom B (T a) J)
    have : Surjective p := ⟨fun x ↦ by
      have : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
        rw [range_comap_of_surjective (B ⧸ J) (Ideal.Quotient.mk J)
          Ideal.Quotient.mk_surjective, Ideal.mk_ker]
        exact hJ x
      exact this⟩
    have : Surjective s := MorphismProperty.of_isPullback (P := @Surjective) hpb ‹_›
    refine ⟨n, ⟨isoOfAdicUpperStarIso s ?_⟩⟩
    exact ((adicUpperStarComp l s _).app G).symm ≪≫ (adicUpperStarCongr l hpb.w.symm).app G ≪≫
      (adicUpperStarComp l _ p).app G ≪≫ e ≪≫ (AdicSheaf.freeUpperStarIso l (Fin n) s).symm
  · -- the basic opens `D(f b)` are empty
    have : IsEmpty (Spec (.of (Localization.Away (f b)))) := ⟨fun x ↦ by
      have h := hJ (PrimeSpectrum.comap (algebraMap B (Localization.Away (f b))) x) (hfJ b)
      exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.Away.algebraMap_isUnit _))⟩
    have : IsEmpty (closedLiftCoverObj (fun a ↦ (T a : Type u)) f (.inr b)) := this
    exact ⟨0, ⟨isoOfIsEmpty _ _⟩⟩


/-- **Nil-invariance of lissity over an affine scheme.** For a surjective closed immersion
`i : Z ⟶ Spec R`, a sheaf `G` on `Spec R` is lisse as soon as `i^* G` is: `Z` is the spectrum
of a quotient `R ⧸ I` with `I` contained in every prime ideal
(`IsAdicLisseSheaf.of_adicUpperStar_specMap_quotientMk`). -/
theorem IsAdicLisseSheaf.of_adicUpperStar_of_surjective_of_spec {R : CommRingCat.{u}}
    {Z : Scheme.{u}} (i : Z ⟶ Spec R) [IsClosedImmersion i] [Surjective i]
    {G : AdicSheaf l (Spec R)} (hG : IsAdicLisseSheaf ((i)^*ᵃ[l].obj G)) :
    IsAdicLisseSheaf G := by
  obtain ⟨I, e, rfl⟩ := IsClosedImmersion.Spec_iff.1 ‹IsClosedImmersion i›
  refine IsAdicLisseSheaf.of_adicUpperStar_specMap_quotientMk I (fun q x hx ↦ ?_)
    (hG.upperStar_of_comp (e.inv_hom_id_assoc _))
  obtain ⟨z, hz⟩ := (e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).surjective q
  rw [← hz, Scheme.Hom.comp_apply]
  change Ideal.Quotient.mk I x ∈ (e.hom z).asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
  exact zero_mem _

/-- **Nil-invariance of lissity.** Let `i : Z ⟶ Y` be a surjective closed immersion, for
instance the inclusion of the reduced subscheme. A sheaf `G` of `ℚ̄_ℓ`-modules on `Y_proét` is
lisse as soon as its pullback `i^* G` is.

Lissity being Zariski local, we may assume `Y = Spec B` affine, so that `Z = Spec (B ⧸ J)` with
`J` contained in every prime ideal. A trivialising cover of `i^* G` is refined by finitely many
`Spec C_a`, `C_a` ind-étale over `B ⧸ J`. Their closed lifts `Spec H_B(C_a)` together with
basic opens `D(f)`, `f ∈ J`, which are empty, form a pro-étale cover of `Y`
(`exists_ofArrows_closedLiftCover_mem_proetalePrecoverage`), and `Spec C_a ⟶ Spec H_B(C_a)` is
a surjective closed immersion, being the base change of `i`. Pullback along a surjective closed
immersion is fully faithful on isomorphism classes
(`isoOfAdicUpperStarIso`), so the trivialisation of `i^* G` on `Spec C_a` lifts to one of `G` on
`Spec H_B(C_a)`. -/
theorem IsAdicLisseSheaf.of_adicUpperStar_of_surjective {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [Surjective i] {G : AdicSheaf l Y}
    (hG : IsAdicLisseSheaf ((i)^*ᵃ[l].obj G)) : IsAdicLisseSheaf G := by
  refine IsAdicLisseSheaf.of_forall_exists_opens fun y ↦ ?_
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  refine ⟨W, hyW, ?_⟩
  let i' := (i ∣_ W) ≫ hW.isoSpec.hom
  have : Surjective (i ∣_ W) := by
    refine ⟨fun w ↦ ?_⟩
    obtain ⟨z, hz⟩ := i.surjective w.1
    exact ⟨⟨z, show i z ∈ W from hz ▸ w.2⟩, Subtype.ext (by simp [hz])⟩
  have h₁ : IsAdicLisseSheaf ((i' ≫ hW.isoSpec.inv ≫ W.ι)^*ᵃ[l].obj G) :=
    hG.upperStar_of_comp (f := (i ⁻¹ᵁ W).ι) (by simp [i', morphismRestrict_ι])
  have h₂ := IsAdicLisseSheaf.upperStar_upperStar_of_comp rfl h₁
  have h₃ : IsAdicLisseSheaf ((i')^*ᵃ[l].obj ((hW.isoSpec.inv)^*ᵃ[l].obj ((W.ι)^*ᵃ[l].obj G))) :=
    h₂.of_iso ((i')^*ᵃ[l].mapIso ((adicUpperStarComp l _ _).app G))
  exact IsAdicLisseSheaf.of_upperStar_of_isIso hW.isoSpec.inv
    (IsAdicLisseSheaf.of_adicUpperStar_of_surjective_of_spec i' h₃)


/-- A version of `IsAdicLisseSheaf.upperStar_opensι_of_subset_range` without reducedness: the
restriction of a sheaf to an open subscheme `W` contained in the image of an immersion `f` on
which the sheaf is lisse, is lisse. The restriction `f ∣_ W` of `f` is a surjective closed
immersion, along which lissity descends (`IsAdicLisseSheaf.of_adicUpperStar_of_surjective`). -/
theorem IsAdicLisseSheaf.upperStar_opensι_of_subset_range' {X : Scheme.{u}} {F : AdicSheaf l X}
    {Z : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] (hf : IsAdicLisseSheaf ((f)^*ᵃ[l].obj F))
    (W : X.Opens) (hW : (W : Set X) ⊆ Set.range f) :
    IsAdicLisseSheaf ((W.ι)^*ᵃ[l].obj F) := by
  have hsurj : Surjective (f ∣_ W) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨z, hz⟩ := hW y.2
    exact ⟨⟨z, show f z ∈ W from hz ▸ y.2⟩, Subtype.ext (by simp [hz])⟩
  have : IsClosedImmersion (f ∣_ W) := by
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    rw [Set.range_eq_univ.2 hsurj.surj]
    exact isClosed_univ
  exact IsAdicLisseSheaf.of_adicUpperStar_of_surjective (f ∣_ W)
    (IsAdicLisseSheaf.upperStar_upperStar_of_comp (morphismRestrict_ι f W)
      (hf.upperStar_of_comp rfl))

/-- A version of `IsAdicConstructibleSheaf.exists_opens_isAdicLisseSheaf` without reducedness:
on a scheme whose underlying space is Noetherian, a constructible `ℓ`-adic sheaf is lisse on an
open neighbourhood of every generic point of an irreducible component. -/
theorem IsAdicConstructibleSheaf.exists_opens_isAdicLisseSheaf' {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F)
    {ξ : X} (hξ : ξ ∈ genericPoints X) :
    ∃ W : X.Opens, ξ ∈ W ∧ IsAdicLisseSheaf ((W.ι)^*ᵃ[l].obj F) := by
  obtain ⟨W, j, hj, ⟨w, rfl⟩, ι', hι', Z, i, hi, -, hcover, hl⟩ := hF ξ
  obtain ⟨k, ⟨z, hz⟩, -⟩ := hcover w
  have hs : Topology.IsConstructible (Set.range (i k ≫ j)) :=
    (i k ≫ j).isLocallyClosed_range.isConstructible_of_noetherianSpace
  obtain ⟨u, hu, hξu, hus⟩ := hs.exists_isOpen_mem_subset hξ ⟨z, by simp [hz]⟩
  exact ⟨⟨u, hu⟩, hξu, IsAdicLisseSheaf.upperStar_opensι_of_subset_range' (i k ≫ j)
    ((hl k).of_iso ((adicUpperStarComp l _ _).app F).symm) ⟨u, hu⟩ hus⟩

end AlgebraicGeometry.ProEtale
