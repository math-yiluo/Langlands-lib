/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.Sites.PullbackIsoOfLocallyGenerated
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Pullback of the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.UpperStar`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The pullback of the constant sheaf `Λ_V` along an arbitrary morphism of schemes
`g : W ⟶ V` is the constant sheaf `Λ_W` (Bhatt–Scholze, *The pro-étale topology for
schemes*, Lemma 4.2.12 and §6.8).

For a weakly étale `g` the pullback is restriction along the localization functor
`W.ProEt ⥤ V.ProEt` (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), and
both sheaves have the continuous functions on `T` as sections over `T → W`.

For a general `g`, the canonical morphism `g^* Λ_V ⟶ Λ_W`, adjoint to precomposition
`Λ_V ⟶ g_* Λ_W` with the projections `V' ×_V W ⟶ V'`, is an isomorphism by the criterion
`CategoryTheory.isIso_homEquiv_symm_of_locally_generated`:

- every section of `Λ_W` is locally the pullback of the tautological function on a constant
  profinite scheme `Spec (LocallyConstant K R)` over an affine open `Spec R ⊆ V`, for `K` a
  compact subset of `Λ`; this scheme is weakly étale
  over `Spec R` (`AlgebraicGeometry.ProEtale.exists_openImmersion_eq_comp_fst_field`);
- a section of `Λ_V` vanishing on the image of a map factors, locally, through its zero
  locus, which is weakly étale over `V`, being affine-locally the spectrum of a localization at
  idempotents (`AlgebraicGeometry.ProEtale.exists_opens_factor_of_eq_zero_field`).

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIsoOfWeaklyEtale`: `g^* Λ_V ≅ Λ_W`
  for a weakly étale `g`, computed by restriction.
- `AlgebraicGeometry.ProEtale.fieldConstantSheafToLowerStar`: the comparison
  `Λ_V ⟶ g_* Λ_W`.
- `AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIso`: `g^* Λ_V ≅ Λ_W` for an arbitrary
  `g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ] {V W : Scheme.{u}}

/-- The restriction of the constant sheaf along a weakly étale `g : W ⟶ V` is the
constant sheaf: both have the continuous functions on `T` as sections
over `T → W`. -/
noncomputable def fieldConstantSheafLocalizationRestrictionIso (g : W ⟶ V) (h : WeaklyEtale g) :
    (localizationRestriction (FieldCoefficients.{u} Λ) g h).obj (fieldConstantSheaf Λ V) ≅
      fieldConstantSheaf Λ W :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _)

/-- The pullback of the constant sheaf along a weakly étale `g : W ⟶ V` is the constant
`Λ`-adic sheaf, the pullback being restriction in this case. -/
noncomputable def upperStarFieldConstantSheafIsoOfWeaklyEtale (g : W ⟶ V) [h : WeaklyEtale g] :
    (g)^*[FieldCoefficients.{u} Λ].obj (fieldConstantSheaf Λ V) ≅ fieldConstantSheaf Λ W :=
  (upperStarIsoLocalizationRestriction _ g h).app _ ≪≫
    fieldConstantSheafLocalizationRestrictionIso Λ g h

section General

variable {Λ} (g : W ⟶ V)

/-- **Zero loci are pro-étale locally weakly étale.** Let `t` be a continuous function on
`V' : V.ProEt` vanishing on the image of `φ : U ⟶ V' ×_V W`. Then every point of `U` has an open
neighbourhood `O` on which `φ` factors through `V'' ×_V W` for a morphism `a : V'' ⟶ V'` of the
pro-étale site with `t ∘ a = 0`. On an affine open `Spec R ⊆ V'`, the zero locus of `t` is the
intersection of the clopen subsets `|t| < 1 / (n + 1)` (the field `Λ` being ultrametric),
cut out by idempotents `e n`, and `V''` is the spectrum of the localization of `R` at the `e n`,
which is weakly étale over `R`. -/
lemma exists_opens_factor_of_eq_zero_field (V' : V.ProEt) (t : C(V'.left, Λ))
    (U : W.ProEt)
    (φ : U ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V')
    (ht : ∀ x, t ((pullback.fst V'.hom g).base (φ.left.base x)) = 0) (x : U.left) :
    ∃ O : U.left.Opens, x ∈ O ∧ ∃ (V'' : V.ProEt) (a : V'' ⟶ V')
      (φ' : Scheme.ProEt.ofOpenImmersion U O.ι ⟶
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V''),
      (∀ y, t (a.left.base y) = 0) ∧
        φ' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map a =
          Scheme.ProEt.ofOpenImmersionHom U O.ι ≫ φ := by
  obtain ⟨R, f, hf, hy, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := V'.left) (x := (pullback.fst V'.hom g).base (φ.left.base x)) (U := ⊤) trivial
  let O : U.left.Opens := (φ.left ≫ pullback.fst V'.hom g) ⁻¹ᵁ f.opensRange
  have hxO : x ∈ O := hy
  let m : (O : Scheme) ⟶ Spec R :=
    IsOpenImmersion.lift f (O.ι ≫ φ.left ≫ pullback.fst V'.hom g) (by
      rintro _ ⟨y, rfl⟩
      exact y.2)
  have hm : m ≫ f = O.ι ≫ φ.left ≫ pullback.fst V'.hom g := IsOpenImmersion.lift_fac _ _ _
  let t' : C(PrimeSpectrum R, Λ) := t.comp ⟨f.base, f.base.hom.continuous⟩
  have hD (n : ℕ) : IsClopen (t' ⁻¹' Metric.ball 0 (1 / (n + 1))) :=
    (IsUltrametricDist.isClopen_ball 0 _).preimage t'.continuous
  choose e he hDe using fun n ↦ PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hD n)
  let M : Submonoid R := Submonoid.closure (Set.range e)
  have ht' (y : O) : t' (m.base y) = 0 := by
    have := congrArg (fun h ↦ h.base y) hm
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    simp only [t', ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    rw [this]
    exact ht _
  have hM : ∀ r ∈ M, ∀ y : (O : Scheme), m y ∈ PrimeSpectrum.basicOpen r := by
    intro r hr y
    induction hr using Submonoid.closure_induction with
    | mem r hr =>
      obtain ⟨n, rfl⟩ := hr
      rw [← SetLike.mem_coe, ← hDe n]
      simp only [Set.mem_preimage, ht' y, Metric.mem_ball, dist_self]
      positivity
    | one => simp
    | mul r s _ _ hr hs =>
      rw [PrimeSpectrum.basicOpen_mul]
      exact ⟨hr, hs⟩
  obtain ⟨m', hm'⟩ := exists_comp_SpecMap_algebraMap_localization m M hM
  have := V'.prop
  let V'' : V.ProEt := Scheme.ProEt.mk
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) ≫ f ≫ V'.hom)
  let a : V'' ⟶ V' := MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) ≫ f) (by simp [V''])
  refine ⟨O, hxO, V'', a, MorphismProperty.Over.homMk
    (pullback.lift m' (O.ι ≫ U.hom) ?_) (pullback.lift_snd _ _ _), ?_, ?_⟩
  · have hφ : φ.left ≫ pullback.snd V'.hom g = U.hom := by simpa using φ.w
    change m' ≫ Spec.map _ ≫ f ≫ V'.hom = (O.ι ≫ U.hom) ≫ g
    rw [reassoc_of% hm', reassoc_of% hm, pullback.condition, ← hφ]
    simp only [Category.assoc]
  · intro y
    let p := (Spec.map (CommRingCat.ofHom (algebraMap R (Localization M)))).base y
    have hp (n : ℕ) : t' p ∈ Metric.ball 0 (1 / (n + 1)) := by
      rw [← Set.mem_preimage, hDe n]
      change e n ∉ Ideal.comap (algebraMap R (Localization M)) y.asIdeal
      rw [Ideal.mem_comap]
      exact fun h ↦ y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.map_units (Localization M)
          (⟨e n, Submonoid.subset_closure ⟨n, rfl⟩⟩ : M)))
    change t' p = 0
    by_contra h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 h)
    have := hp n
    rw [Metric.mem_ball, dist_zero_right] at this
    exact lt_asymm hn this
  · have hφ : φ.left ≫ pullback.snd V'.hom g = U.hom := by simpa using φ.w
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift m' (O.ι ≫ U.hom) _ ≫ pullback.lift (pullback.fst V''.hom g ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) ≫ f))
        (pullback.snd V''.hom g) _ = O.ι ≫ φ.left
    apply pullback.hom_ext
    · simp [reassoc_of% hm', hm]
    · simp [hφ]


/-- **The sections of `Λ_W` are locally pulled back from `Λ_V`.** Every point of
`U : W.ProEt` has an affine open neighbourhood `Spec B` on which a continuous function `s`
on `U` is `t ∘ fst ∘ φ` for some `V' : V.ProEt`, a continuous function `t` on `V'` and
`φ : Spec B ⟶ V' ×_V W`. Here `V'` is the constant profinite scheme `Spec R × K` over an affine
open `Spec R ⊆ V`, with `K = s(Spec B)` compact in `Λ`,
that is the spectrum of the weakly étale `R`-algebra `LocallyConstant K R`; `t` is the
projection to `K`, and `φ` is given by `s` (`LocallyConstant.liftPrimeSpectrum`). -/
lemma exists_openImmersion_eq_comp_fst_field (U : W.ProEt)
    (s : fieldFunctions Λ U.left)
    (x : U.left) :
    ∃ (B : CommRingCat.{u}) (j : Spec B ⟶ U.left) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ ∃ (V' : V.ProEt) (t : fieldFunctions Λ V'.left)
        (φ : Scheme.ProEt.ofOpenImmersion U j ⟶
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V'),
        ∀ y, (s : C(U.left, Λ)) (j y) =
          (t : C(V'.left, Λ)) ((pullback.fst V'.hom g) (φ.left y)) := by
  let N : Set U.left := Set.univ
  have hN : N ∈ 𝓝 x := Filter.univ_mem
  obtain ⟨R, f, hf, hv, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := V) (x := g (U.hom x)) (U := ⊤) trivial
  let O : U.left.Opens := ⟨interior N, isOpen_interior⟩ ⊓ (U.hom ≫ g) ⁻¹ᵁ f.opensRange
  have hxO : x ∈ O := ⟨mem_interior_iff_mem_nhds.2 hN, hv⟩
  obtain ⟨B, j, hj, hxj, hjO⟩ := Scheme.exists_affine_mem_range_and_range_subset hxO
  let m : Spec B ⟶ Spec R := IsOpenImmersion.lift f (j ≫ U.hom ≫ g) (by
    rintro _ ⟨y, rfl⟩
    exact (hjO ⟨y, rfl⟩).2)
  have hm : m ≫ f = j ≫ U.hom ≫ g := IsOpenImmersion.lift_fac _ _ _
  let K : Set Λ := Set.range fun y : Spec B ↦ (s : C(U.left, Λ)) (j y)
  have hKc : IsCompact K := isCompact_range ((s : C(U.left, Λ)).continuous.comp
    j.base.hom.continuous)
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let σ : C(PrimeSpectrum B, K) :=
    ⟨fun y ↦ ⟨(s : C(U.left, Λ)) (j y), y, rfl⟩,
      ((s : C(U.left, Λ)).continuous.comp j.base.hom.continuous).subtype_mk _⟩
  let L := LocallyConstant.liftPrimeSpectrum (Spec.preimage m).hom σ
  let V' : V.ProEt := Scheme.ProEt.mk
    (Spec.map (CommRingCat.ofHom (algebraMap R (LocallyConstant K R))) ≫ f)
  let τ : C(PrimeSpectrum (LocallyConstant K R), Λ) :=
    ⟨fun q ↦ ((LocallyConstant.homeomorphPrimeSpectrum.symm q).1 : Λ),
      continuous_subtype_val.comp (continuous_fst.comp
        LocallyConstant.homeomorphPrimeSpectrum.symm.continuous)⟩
  have hτ : τ ∈ fieldFunctions Λ V'.left := Algebra.mem_top
  have hL : (CommRingCat.ofHom (algebraMap R (LocallyConstant K R)) ≫ CommRingCat.ofHom L) =
      Spec.preimage m := by
    ext r
    exact LocallyConstant.liftPrimeSpectrum_algebraMap _ _ r
  refine ⟨B, j, hj, hxj, V', ⟨τ, hτ⟩, MorphismProperty.Over.homMk
    (pullback.lift (Spec.map (CommRingCat.ofHom L)) (j ≫ U.hom) ?_) (pullback.lift_snd _ _ _),
    fun y ↦ ?_⟩
  · change Spec.map _ ≫ Spec.map _ ≫ f = _
    rw [← Spec.map_comp_assoc, hL, Spec.map_preimage, hm, Category.assoc]
  · change _ = τ ((pullback.lift (Spec.map (CommRingCat.ofHom L)) (j ≫ U.hom) _ ≫
      pullback.fst V'.hom g) y)
    rw [pullback.lift_fst]
    change _ = ((LocallyConstant.homeomorphPrimeSpectrum.symm
      (PrimeSpectrum.comap L y)).1 : Λ)
    rw [LocallyConstant.comap_liftPrimeSpectrum, ← LocallyConstant.homeomorphPrimeSpectrum_apply,
      Homeomorph.symm_apply_apply]
    rfl


variable (Λ) in
/-- The comparison `Λ_V ⟶ g_* Λ_W`: precomposition with `V' ×_V W ⟶ V'`. -/
noncomputable def fieldConstantSheafToLowerStar :
    fieldConstantSheaf Λ V ⟶ (g)_*[FieldCoefficients.{u} Λ].obj (fieldConstantSheaf Λ W) :=
  ⟨{ app V' := ModuleCat.ofHom (FieldCoefficients.uliftLinearMap
        (fieldFunctionsComp Λ (pullback.fst V'.unop.hom g).base.hom))
     naturality V₁ V₂ a := by
       ext x
       refine ULift.ext (Subtype.ext (ContinuousMap.ext fun y ↦ ?_))
       change x.down.1 (a.unop.left (pullback.fst _ g y)) =
         x.down.1 (pullback.fst _ g (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
           a.unop).left y))
       have key : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map a.unop).left ≫
           pullback.fst _ g = pullback.fst _ g ≫ a.unop.left :=
         pullback.lift_fst _ _ _
       rw [← Scheme.Hom.comp_apply, ← key]
       rfl }⟩


omit [IsUltrametricDist Λ] in
/-- Two sections of `Λ` are equal if their underlying functions agree. -/
lemma fieldConstantSheaf_ext {X : Scheme.{u}} {U : X.ProEt}
    {s s' : (fieldConstantSheaf Λ X).obj.obj (op U)}
    (h : ∀ y, s.down.1 y = s'.down.1 y) :
    s = s' :=
  ULift.ext (Subtype.ext (ContinuousMap.ext h))

variable (Λ) in
/-- The canonical morphism `g^* Λ_V ⟶ Λ_W`, adjoint to
`AlgebraicGeometry.ProEtale.fieldConstantSheafToLowerStar`. -/
noncomputable def upperStarFieldConstantSheafHom :
    (g)^*[FieldCoefficients.{u} Λ].obj (fieldConstantSheaf Λ V) ⟶ fieldConstantSheaf Λ W :=
  ((upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) g).homEquiv _ _).symm
    (fieldConstantSheafToLowerStar Λ g)

/-- The canonical morphism `g^* Λ_V ⟶ Λ_W` is an isomorphism, by the criterion
`CategoryTheory.isIso_homEquiv_symm_of_locally_generated`: sections of `Λ_W` are locally
pulled back from `Λ_V` (`AlgebraicGeometry.ProEtale.exists_openImmersion_eq_comp_fst_field`), and
relations between them hold locally on `V`
(`AlgebraicGeometry.ProEtale.exists_opens_factor_of_eq_zero_field`). -/
instance isIso_upperStarFieldConstantSheafHom : IsIso (upperStarFieldConstantSheafHom Λ g) := by
  refine isIso_homEquiv_symm_of_locally_generated
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (fieldConstantSheafToLowerStar Λ g)
    (fun U s ↦ ?_) (fun V' t U φ ht ↦ ?_) (upperStarLowerStarAdjunction _ g)
  · let S : Sieve U :=
      { arrows _ u := ∃ (V' : V.ProEt) (t : (fieldConstantSheaf Λ V).obj.obj (op V'))
          (φ : _ ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V'),
          (fieldConstantSheaf Λ W).obj.map u.op s = (fieldConstantSheaf Λ W).obj.map φ.op
            ((fieldConstantSheafToLowerStar Λ g).hom.app (op V') t)
        downward_closed := by
          rintro _ _ u ⟨V', t, φ, h⟩ v
          refine ⟨V', t, v ≫ φ, ?_⟩
          rw [op_comp, Functor.map_comp, ModuleCat.comp_apply, h, op_comp, Functor.map_comp,
            ModuleCat.comp_apply] }
    refine ⟨S, ?_, fun _ _ h ↦ h⟩
    choose B j hj hxj V' t φ hφ using exists_openImmersion_eq_comp_fst_field (Λ := Λ) g U s.down
    exact Scheme.ProEt.mem_topology_of_openImmersion S j (fun x ↦ ⟨x, hxj x⟩) fun x ↦
      ⟨V' x, ULift.up (t x), φ x, fieldConstantSheaf_ext fun y ↦ hφ x y⟩
  · have hpt (x : U.left) : t.down.1 ((pullback.fst V'.hom g) (φ.left x)) = 0 :=
      congrArg (fun s ↦ s.down.1 x) ht
    let S : Sieve U :=
      { arrows _ u := ∃ (V'' : V.ProEt) (a : V'' ⟶ V')
          (φ' : _ ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V''),
          (fieldConstantSheaf Λ V).obj.map a.op t = 0 ∧
            φ' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map a = u ≫ φ
        downward_closed := by
          rintro _ _ u ⟨V'', a, φ', h, h'⟩ v
          exact ⟨V'', a, v ≫ φ', h, by rw [Category.assoc, h', Category.assoc]⟩ }
    refine ⟨S, ?_, fun _ _ h ↦ h⟩
    choose O hxO V'' a φ' hz heq using exists_opens_factor_of_eq_zero_field g V' t.down.1 U φ hpt
    exact Scheme.ProEt.mem_topology_of_openImmersion S (fun x ↦ (O x).ι)
      (fun x ↦ ⟨x, by simpa using hxO x⟩) fun x ↦
        ⟨V'' x, a x, φ' x, fieldConstantSheaf_ext fun y ↦ hz x y, heq x⟩

variable (Λ) in
/-- **The pullback of the constant sheaf is the constant sheaf**
(Bhatt–Scholze, Lemma 4.2.12): for an arbitrary morphism `g : W ⟶ V`, `g^* Λ_V ≅ Λ_W`. -/
noncomputable def upperStarFieldConstantSheafIso :
    (g)^*[FieldCoefficients.{u} Λ].obj (fieldConstantSheaf Λ V) ≅ fieldConstantSheaf Λ W :=
  asIso (upperStarFieldConstantSheafHom Λ g)

end General

end AlgebraicGeometry.ProEtale
