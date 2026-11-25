/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading
public import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

/-!
# Vanishing in the universal curve test

This is the positive half of the proof of smooth base change: on a curve-test datum
`AlgebraicGeometry.Etale.CurveTestDatum` the higher direct images of the constant sheaf
`Λ/dΛ` along the geometric generic fibre vanish in positive degrees. Together with the
counterexample chain, which produces a curve-test datum where they do not, it gives the
contradiction that proves the theorem.

## Implementation notes

The statement is phrased on a curve-test datum rather than on loose data, so that it is
literally about the same object as `AlgebraicGeometry.Etale.exists_curveTestDatum`. In
particular the geometric point `Spec K ⟶ S₀` of the datum factors through the generic point:
the proof in degree one compares `H¹` of the generic fibre over the function field with `H¹`
over `K` and then spreads a cover out from the generic fibre, neither of which is available
at a closed point.

The proof works with the `AddCommGrpCat`-valued cohomology `H^q(-, ℤ/e)` of the fibres
`Y₀ ×_{X₀} U` for `U` affine étale over `X₀` and `e ∣ d`: by
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists` (blueprint
`proposition-base-change-larger-algebraically-closed`) it suffices that every such class dies on an
étale cover of `U`. In degrees `q ≥ 2` the classes vanish outright, `Y₀ ×_{X₀} U` being a smooth
affine curve over `K`. In degree one the class is killed by a torsor spread out from the generic
fibre, after reducing to a base with a section by slicing. Only the *vanishing* of pulled-back
classes is used, which is why `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap_eq_zero_iff`
suffices to compare pullbacks along composites.

## Main statements

- `AlgebraicGeometry.Etale.exists_etaleTorsor_cohomologyMap_eq_zero`: over a base with a
  section, a class of `H¹` of the geometric generic fibre dies on a torsor over the curve.
- `AlgebraicGeometry.Etale.CurveTestDatum.exists_cover_cohomologyMap_eq_zero`: the degree-one
  classes die on étale covers.
- `AlgebraicGeometry.Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf`: on a
  curve-test datum the higher direct images `R^q h_* (Λ/dΛ)` vanish for `q ≥ 1`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The degree-one step of blueprint `proposition-base-change-larger-algebraically-closed--1`, over
a base with a section.

Let `W` be an affine integral normal scheme with algebraically closed function field `L`, let
`c : C ⟶ W` be affine and smooth of relative dimension one with geometrically connected fibres
and a section `σ`, let `K` be an algebraically closed extension of `L` and let `Y` be the fibre
of `c` over the geometric generic point `Spec K ⟶ W`. Let `e` be invertible on `W`. Then every
class `ξ ∈ H¹(Y, ℤ/e)` is killed by a `ℤ/e`-torsor `T` over `C`: it dies after pullback to any
scheme `Z` over `Y` whose map to `C` lifts to `T`.

By `AlgebraicGeometry.bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension`
(blueprint `theorem-cohomology-curves--6`) the class comes from the generic fibre
`C_L`, where it is represented by a torsor `t`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`). The torsor
has an `L`-point above the generic point of the section, since `H¹(Spec L, ℤ/e) = 0`, so it
spreads out to a torsor `T` over `C`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre`). -/
theorem Etale.exists_etaleTorsor_cohomologyMap_eq_zero {W C : Scheme.{u}} [IsAffine W]
    [IsIntegral W] (hW : ∀ x : W, IsIntegrallyClosed (W.presheaf.stalk x))
    [IsAlgClosed W.functionField] (c : C ⟶ W) [IsAffineHom c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyConnected c] (σ : W ⟶ C) (hσ : σ ≫ c = 𝟙 W) {K : Type u} [Field K]
    [IsAlgClosed K] (i : W.functionField ⟶ CommRingCat.of K) {Y : Scheme.{u}}
    (eY : Y ⟶ Spec (.of K)) (hY : Y ⟶ C)
    (sq : IsPullback eY hY (Spec.map i ≫ W.fromSpecStalk (genericPoint W)) c) (e : ℕ)
    [NeZero e] (he : IsUnit (e : Γ(W, ⊤))) (ξ : Sheaf.H (Y.constantZMod e) 1) :
    ∃ T : Scheme.EtaleTorsor (ULift.{u + 1} (ZMod e)) C, ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ Y)
      (w : Z ⟶ T.P), z ≫ hY = w ≫ T.π → Etale.cohomologyMap z _ 1 ξ = 0 := by
  let L := W.functionField
  let : Algebra L K := i.hom.toAlgebra
  let η := W.fromSpecStalk (genericPoint W)
  -- the generic fibre `C_L` of `c`
  have hCη : IsPullback (pullback.snd c η) (pullback.fst c η) η c :=
    (IsPullback.of_hasPullback c η).flip
  let qL : pullback c η ⟶ Spec (.of L) := pullback.snd c η
  have : SmoothOfRelativeDimension 1 qL :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hCη.flip inferInstance
  have : IsAffineHom qL := MorphismProperty.of_isPullback hCη.flip inferInstance
  -- `Y` is the base change of `C_L` to `K`
  have hi : CommRingCat.ofHom (algebraMap L K) = i := rfl
  let yL : Y ⟶ pullback c η := pullback.lift hY (eY ≫ Spec.map i) (by
    rw [Category.assoc]
    exact sq.w.symm)
  have hyL : IsPullback yL eY qL (Spec.map (CommRingCat.ofHom (algebraMap L K))) := by
    rw [hi]
    exact IsPullback.of_right (h₁₂ := pullback.fst c η) (by simpa [yL] using sq.flip)
      (by simp [yL, qL]) hCη.flip
  let φ := hyL.isoPullback
  have hφ : φ.hom ≫ pullback.fst _ _ = yL := hyL.isoPullback_hom_fst
  -- the class comes from the generic fibre
  have hL : ((e : ℕ) : L) ≠ 0 := by
    simpa using (he.map (W.presheaf.germ ⊤ (genericPoint W) trivial).hom).ne_zero
  have hbij := bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension qL (k' := K) e
    hL 1
  let fstP := pullback.fst qL (Spec.map (CommRingCat.ofHom (algebraMap L K)))
  let ι₁ := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} φ.inv).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod e)))
  let ι₂ := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} fstP).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod e)))
  obtain ⟨ξL, hξL⟩ := hbij.2
    (Sheaf.H.map (ι₁.hom ≫ ι₂.inv) 1 (Etale.cohomologyMap φ.inv _ 1 ξ))
  -- it is represented by a torsor over the generic fibre
  obtain ⟨t, ht⟩ := Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff
    (ULift.{u + 1} (ZMod e)) ξL
  -- which has a point above the generic point of the section
  let σL : Spec (.of L) ⟶ pullback c η := pullback.lift (η ≫ σ) (𝟙 _) (by simp [hσ])
  have hpt : ∃ z : Spec (.of L) ⟶ t.P, z ≫ t.π = σL := by
    rw [← ht]
    have := Scheme.projective_constantSheaf_of_isSepClosed (L : Type u)
    have hsub (G : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
        Subsingleton (Sheaf.H G (0 + 1)) :=
      Abelian.Ext.subsingleton_of_projective _ _ _
    exact (hsub _).elim _ _
  -- so it spreads out to a torsor over `C`
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  obtain ⟨T, ψ, hψ, -⟩ := Scheme.EtaleTorsor.exists_isPullback_of_genericFibre hW c σ hσ
    (ULift.{u + 1} (ZMod e)) (by simpa using he) qL (pullback.fst c η) hCη σL
    (by simp [σL, qL]; rfl) (by simp [σL, η]) t hpt
  refine ⟨T, fun Z z w hzw ↦ ?_⟩
  have hs : hψ.lift w (z ≫ yL) (by simp [yL, hzw]) ≫ t.π = z ≫ yL := hψ.lift_snd _ _ _
  have h₀ := (ht (z ≫ yL)).2 ⟨_, hs⟩
  have h₁ := (Etale.cohomologyMap_cohomologyMap_eq_zero_iff (z ≫ φ.hom) fstP (z ≫ yL)
    (by simp [fstP, hφ]) _ ξL).2 h₀
  rw [hξL] at h₁
  exact (Etale.cohomologyMap_cohomologyMap_eq_zero_iff (z ≫ φ.hom) φ.inv z (by simp) _ ξ).1
    ((Etale.cohomologyMap_map_eq_zero_iff _ (ι₁.hom ≫ ι₂.inv) 1 _).1 h₁)

attribute [local instance] Etale.CurveTestDatum.isAffine_base
  Etale.CurveTestDatum.isIntegral_base Etale.CurveTestDatum.isAlgClosed_functionField
  Etale.CurveTestDatum.isAffineHom Etale.CurveTestDatum.smoothOfRelativeDimension_one
  Etale.CurveTestDatum.field Etale.CurveTestDatum.isAlgClosed

/-- An open `W` of the base of a curve-test datum, given by an open immersion `ι : W ⟶ S₀`,
is again normal with algebraically closed function field, and the geometric generic point
`Spec K ⟶ S₀` of the datum factors through the generic point of `W`. -/
theorem Etale.CurveTestDatum.isIntegrallyClosed_and_isAlgClosed_and_exists_of_isOpenImmersion
    (D : Etale.CurveTestDatum.{u}) {W : Scheme.{u}}
    [IsIntegral W] (ι : W ⟶ D.S₀) [IsOpenImmersion ι] :
    (∀ x : W, IsIntegrallyClosed (W.presheaf.stalk x)) ∧ IsAlgClosed W.functionField ∧
      ∃ iW : W.functionField ⟶ CommRingCat.of D.K,
        (Spec.map iW ≫ W.fromSpecStalk (genericPoint W)) ≫ ι =
          Spec.map D.i ≫ D.S₀.fromSpecStalk (genericPoint D.S₀) := by
  have hst (x : W) : IsIso (ι.stalkMap x) := (IsOpenImmersion.iff_isIso_stalkMap.1 ‹_›).2 x
  have hgen : ι (genericPoint W) = genericPoint D.S₀ := genericPoint_eq_of_isOpenImmersion ι
  refine ⟨fun x ↦ ?_, ?_, ?_⟩
  · have := D.isIntegrallyClosed_stalk (ι x)
    exact .of_equiv (asIso (ι.stalkMap x)).commRingCatIsoToRingEquiv
  · let e : D.S₀.functionField ≅ W.functionField :=
      D.S₀.presheaf.stalkCongr (.of_eq hgen.symm) ≪≫ asIso (ι.stalkMap (genericPoint W))
    exact IsAlgClosed.of_ringEquiv _ _ e.commRingCatIsoToRingEquiv
  · let g := Spec.map D.i ≫ D.S₀.fromSpecStalk (genericPoint D.S₀)
    have hg (y : Spec (.of D.K)) : g y = genericPoint D.S₀ := by
      have : (Spec.map D.i) y = IsLocalRing.closedPoint _ :=
        Subsingleton.elim (α := PrimeSpectrum D.S₀.functionField) _ _
      simp [g, this]
    let gW := IsOpenImmersion.lift ι g (by rintro _ ⟨y, rfl⟩; exact ⟨_, hgen.trans (hg y).symm⟩)
    have hgW : gW ≫ ι = g := IsOpenImmersion.lift_fac _ _ _
    have hpt : gW (IsLocalRing.closedPoint (CommRingCat.of D.K)) = genericPoint W := by
      apply ι.isOpenEmbedding.injective
      rw [hgen, ← Scheme.Hom.comp_apply, hgW, hg]
    have key : ∀ x (hx : x = genericPoint W) (φ : W.presheaf.stalk x ⟶ CommRingCat.of D.K),
        ∃ iW : W.functionField ⟶ CommRingCat.of D.K,
          Spec.map iW ≫ W.fromSpecStalk (genericPoint W) = Spec.map φ ≫ W.fromSpecStalk x := by
      rintro _ rfl φ
      exact ⟨φ, rfl⟩
    obtain ⟨iW, hiW⟩ := key _ hpt (Scheme.stalkClosedPointTo gW)
    refine ⟨iW, ?_⟩
    rw [hiW, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hgW]

/-- The degree-one case of blueprint `proposition-base-change-larger-algebraically-closed--1`: on a
curve-test datum, every class `ξ ∈ H¹(Y₀ ×_{X₀} U, ℤ/e)`, for `e ∣ d` and `U` affine étale over
`X₀`, dies on an étale cover of `U`.

By the slicing lemma `AlgebraicGeometry.Smooth.exists_etaleCover_factorization` (blueprint
`theorem-smooth-base-change-classical-torsion`) `U` is covered by étale `U'` with `U' ⟶ S₀`
factoring as an affine morphism `U' ⟶ V` with geometrically connected fibres and a section, followed
by an étale `V ⟶ S₀`. As `S₀` is normal with algebraically closed function field, `V ⟶ S₀` is a
local isomorphism (`AlgebraicGeometry.Etale.isLocalIso_of_isSepClosed_functionField`, blueprint
`proposition-base-change-larger-algebraically-closed`), so after shrinking `V` to affine opens it is
an open of `S₀`. Over each of these,
`AlgebraicGeometry.Etale.exists_etaleTorsor_cohomologyMap_eq_zero` provides a torsor whose total
space kills the restriction of `ξ`. -/
theorem Etale.CurveTestDatum.exists_cover_cohomologyMap_eq_zero (D : Etale.CurveTestDatum.{u})
    {e : ℕ} [NeZero e] (he : e ∣ D.d) {U : Scheme.{u}} (u : U ⟶ D.X₀) [Etale u] [IsAffine U]
    (ξ : Sheaf.H ((pullback D.h u).constantZMod e) 1) :
    ∃ (ι : Type u) (V : ι → Scheme.{u}) (v : ∀ i, V i ⟶ U), (∀ i, Etale (v i)) ∧
      (∀ x : U, ∃ i y, (v i).base y = x) ∧
      ∀ i, Etale.cohomologyMap (pullback.map D.h (v i ≫ u) D.h u (𝟙 _) (v i) (𝟙 _) (by simp)
        (by simp)) _ 1 ξ = 0 := by
  have : Smooth D.f₀ := SmoothOfRelativeDimension.smooth 1 D.f₀
  have hf : SmoothOfRelativeDimension 1 (u ≫ D.f₀) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (u ≫ D.f₀))
  have : Smooth (u ≫ D.f₀) := SmoothOfRelativeDimension.smooth 1 _
  -- slicing
  obtain ⟨ι, U', p, V, q, r, hp, hpcov, hr, -, hU', hV, hqconn, hsec, hqr⟩ :=
    Smooth.exists_etaleCover_factorization (u ≫ D.f₀)
  have hqaff (i : ι) : IsAffineHom (q i) := by
    have := hU' i
    have := hV i
    infer_instance
  -- each `V i` is locally an affine open of `S₀`
  have hloc (i : ι) (v : V i) : ∃ W : (V i).Opens, v ∈ W ∧ IsAffineOpen W ∧
      IsOpenImmersion (W.ι ≫ r i) := by
    have := hr i
    have := Etale.isLocalIso_of_isSepClosed_functionField D.isIntegrallyClosed_stalk (r i)
    obtain ⟨W₀, hv, hW₀⟩ := IsLocalIso.exists_isOpenImmersion (f := r i) v
    obtain ⟨_, ⟨W, hW, rfl⟩, hvW, hWle⟩ := (V i).isBasis_affineOpens.exists_subset_of_mem_open
      hv W₀.isOpen
    refine ⟨W, hvW, hW, ?_⟩
    rw [← (V i).homOfLE_ι hWle, Category.assoc]
    infer_instance
  choose W hvW hWaff hWι using hloc
  have hkill (i : ι) (v : V i) : ∃ T : Scheme.EtaleTorsor (ULift.{u + 1} (ZMod e))
      (q i ⁻¹ᵁ W i v).toScheme,
      Etale.cohomologyMap (pullback.map D.h ((T.π ≫ (q i ⁻¹ᵁ W i v).ι ≫ p i) ≫ u) D.h u (𝟙 _)
        (T.π ≫ (q i ⁻¹ᵁ W i v).ι ≫ p i) (𝟙 _) (by simp) (by simp)) _ 1 ξ = 0 := by
    have := hWι i v
    have : IsAffine (W i v) := hWaff i v
    have := hqaff i
    have := hqconn i
    have := hp i
    have : Nonempty (W i v) := ⟨⟨v, hvW i v⟩⟩
    have : IsIntegral (W i v) := isIntegral_of_isOpenImmersion ((W i v).ι ≫ r i)
    obtain ⟨hWn, hWalg, iW, hiW⟩ :=
      D.isIntegrallyClosed_and_isAlgClosed_and_exists_of_isOpenImmersion ((W i v).ι ≫ r i)
    let ck := q i ∣_ W i v
    let pk := (q i ⁻¹ᵁ W i v).ι ≫ p i
    have hck : ck ≫ (W i v).ι ≫ r i = pk ≫ u ≫ D.f₀ := by
      simp [ck, pk, morphismRestrict_ι_assoc, hqr i]
    have : SmoothOfRelativeDimension 1 ck := by
      have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
      have h' : SmoothOfRelativeDimension 1 (ck ≫ (W i v).ι ≫ r i) := by
        rw [hck]
        exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (pk ≫ u ≫ D.f₀))
      exact MorphismProperty.of_postcomp (@SmoothOfRelativeDimension 1) (W' := @IsOpenImmersion) ck
        _ (hWι i v) h'
    -- the section
    obtain ⟨s, hs⟩ := hsec i
    have hle : W i v ≤ s ⁻¹ᵁ (q i ⁻¹ᵁ W i v) := by
      rw [← Scheme.Hom.comp_preimage, hs, Scheme.Hom.id_preimage]
    let σk := s.resLE (q i ⁻¹ᵁ W i v) (W i v) hle
    have hσk : σk ≫ ck = 𝟙 _ := by
      rw [← cancel_mono (W i v).ι]
      simp [σk, ck, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, hs]
    -- `e` is invertible on the open
    have he' : IsUnit (e : Γ(W i v, ⊤)) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast he)
        (by simpa using D.isUnit_d.map ((W i v).ι ≫ r i).appTop.hom)
    -- the fibre of `ck` over the geometric generic point
    let m₁ := pullback.map D.h (pk ≫ u) D.h u (𝟙 _) pk (𝟙 _) (by simp) (by simp)
    have sq : IsPullback (pullback.fst D.h (pk ≫ u) ≫ D.e) (pullback.snd D.h (pk ≫ u))
        (Spec.map iW ≫ (W i v).toScheme.fromSpecStalk (genericPoint (W i v))) ck := by
      have big : IsPullback (pullback.fst D.h (pk ≫ u) ≫ D.e) (pullback.snd D.h (pk ≫ u))
          (Spec.map D.i ≫ D.S₀.fromSpecStalk (genericPoint D.S₀)) ((pk ≫ u) ≫ D.f₀) :=
        (IsPullback.of_hasPullback D.h (pk ≫ u)).paste_horiz D.isPullback
      have e₁ : (pk ≫ u) ≫ D.f₀ = ck ≫ (W i v).ι ≫ r i := by rw [hck, Category.assoc]
      rw [e₁, ← hiW] at big
      refine IsPullback.of_right (h₁₂ := 𝟙 _) (h₂₂ := (W i v).ι ≫ r i)
        (v₁₃ := (Spec.map iW ≫ (W i v).toScheme.fromSpecStalk (genericPoint (W i v))) ≫
          (W i v).ι ≫ r i) ?_ ?_ (IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩)
      · rw [Category.comp_id]
        exact big
      · rw [← cancel_mono ((W i v).ι ≫ r i)]
        simpa only [Category.assoc] using big.w
    -- the torsor killing the restricted class
    have := hWalg
    let ι₁ := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} m₁).app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod e)))
    obtain ⟨T, hT⟩ := Etale.exists_etaleTorsor_cohomologyMap_eq_zero hWn ck σk hσk iW _ _ sq e
      he' (Sheaf.H.map ι₁.hom 1 (Etale.cohomologyMap m₁ _ 1 ξ))
    refine ⟨T, ?_⟩
    let m₂ := pullback.map D.h ((T.π ≫ pk) ≫ u) D.h (pk ≫ u) (𝟙 _) T.π (𝟙 _) (by simp)
      (by simp)
    rw [← Etale.cohomologyMap_cohomologyMap_eq_zero_iff m₂ m₁ _
      (by ext <;> simp [m₁, m₂, pk])]
    exact (Etale.cohomologyMap_map_eq_zero_iff m₂ ι₁.hom 1 _).1
      (hT m₂ (pullback.snd _ _) (by simp [m₂]))
  choose T hT using hkill
  refine ⟨Σ i, V i, fun k ↦ (T k.1 k.2).P,
    fun k ↦ (T k.1 k.2).π ≫ (q k.1 ⁻¹ᵁ W k.1 k.2).ι ≫ p k.1, fun k ↦ ?_, fun x ↦ ?_,
    fun k ↦ hT k.1 k.2⟩
  · have := (T k.1 k.2).etale
    have := hp k.1
    infer_instance
  · obtain ⟨i, y, rfl⟩ := hpcov x
    have hy : y ∈ q i ⁻¹ᵁ W i (q i y) := hvW i (q i y)
    have := (T i (q i y)).surjective
    obtain ⟨z, hz⟩ := (T i (q i y)).π.surjective ⟨y, hy⟩
    exact ⟨⟨i, q i y⟩, z, by simp [hz]⟩

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `proposition-base-change-larger-algebraically-closed--1`: Vanishing in the universal
curve test.

For a curve-test datum `D` — an affine smooth relative curve `f₀ : X₀ ⟶ S₀` over an affine
integral normal base with algebraically closed function field, together with the fibre

```
Y₀ ---e---> Spec K
|              |
h              |
v              v
X₀ ---f₀----> S₀
```

over a geometric generic point and an integer `d` invertible on `S₀` — the higher direct
images `R^q h_* (Λ/dΛ)` of the constant sheaf vanish for every `q ≥ 1`.

This is also blueprint `proposition-base-change-larger-algebraically-closed--1`. It is a
recombination of the lemmas of Stacks, Étale Cohomology, Section 59.88 rather than a single tagged
one. By `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists` it
suffices to kill every class of `H^q(Y₀ ×_{X₀} U, ℤ/e)`, `e ∣ d`, on an étale cover of the
affine étale `U ⟶ X₀`. For `q ≥ 2` these groups vanish, `Y₀ ×_{X₀} U` being a smooth affine
curve over `K`
(`AlgebraicGeometry.subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero`,
blueprint `theorem-cohomology-curves--2`); the case `q = 1` is
`AlgebraicGeometry.Etale.CurveTestDatum.exists_cover_cohomologyMap_eq_zero`. -/
theorem Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf
    (D : Etale.CurveTestDatum.{u}) (q : ℤ) (hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ D.h q (Etale.constantModSheaf Λ D.Y₀ D.d)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
  have : IsAffineHom D.h := MorphismProperty.of_isPullback D.isPullback inferInstance
  have : IsAffine D.X₀ := isAffine_of_isAffineHom D.f₀
  have : IsAffine D.Y₀ := isAffine_of_isAffineHom D.h
  have hd₀ : D.d ≠ 0 := by
    intro h
    have := D.isUnit_d
    rw [h, Nat.cast_zero] at this
    exact not_isUnit_zero this
  refine Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists Λ D.h D.d n
    fun e he U u _ _ ξ ↦ ?_
  have : NeZero e := ⟨fun h ↦ hd₀ (Nat.eq_zero_of_zero_dvd (h ▸ he))⟩
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
  · exact D.exists_cover_cohomologyMap_eq_zero he u ξ
  · -- in degrees at least two the class itself vanishes
    refine ⟨PUnit, fun _ ↦ U, fun _ ↦ 𝟙 U, fun _ ↦ inferInstance, fun x ↦ ⟨⟨⟩, x, rfl⟩,
      fun _ ↦ ?_⟩
    have sq := (IsPullback.of_hasPullback D.h u).paste_horiz D.isPullback
    have : SmoothOfRelativeDimension 1 (u ≫ D.f₀) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (u ≫ D.f₀))
    have : SmoothOfRelativeDimension 1 (pullback.fst D.h u ≫ D.e) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq.flip inferInstance
    have := (subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero
      (pullback.fst D.h u ≫ D.e) (NeZero.ne e)).1 n hn
    rw [Subsingleton.elim ξ 0, map_zero]

end AlgebraicGeometry
