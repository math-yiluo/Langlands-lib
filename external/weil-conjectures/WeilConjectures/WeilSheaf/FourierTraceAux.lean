/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.ZetaSeries

/-!
# Auxiliary results for the Fourier trace formula

Bookkeeping on rational points and on Weil complexes used in the proof of the Fourier trace
formula (`AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform`).

For a field extension `K` of `k₀`, `Spec K` is a `k₀`-scheme (`AlgebraicGeometry.specOver`) whose
`L`-rational points are the `k₀`-embeddings `K ⟶ L`. A rational point `y : Spec K ⟶ 𝔸^ι` of the
affine space `𝔸^ι = 𝔸(ι; Spec k₀)` is a morphism of `k₀`-schemes `specOver K ⟶ 𝔸^ι`, along which
we base change the second projection `pr₂ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸^ι`; the `L`-rational points of the
fibre product `AlgebraicGeometry.affineSpacePair.sndFiber y` are the pairs `(φ, x)` of a
`k₀`-embedding `φ : K ⟶ L` and a vector `x ∈ L^ι`, the point `(x, φ(y))` of `𝔸^ι ×_{k₀} 𝔸^ι`
over `φ`. The affine line is the case `ι = PUnit`.

## Main declarations

- `AlgebraicGeometry.specOver`: `Spec K` as a `k₀`-scheme.
- `AlgebraicGeometry.specOver.algHomEquivFieldPoints`: `(specOver K)(L) ≃ (K →ₐ[k₀] L)`.
- `AlgebraicGeometry.specOver.finsum_fieldPoints_eq_nsmul`: a Galois invariant function on the
  `𝔽_{qⁿ}`-rational points of `Spec 𝔽_{qⁿ}` sums to `n` times its value at the tautological point.
- `AlgebraicGeometry.affineSpacePair.sndFiber`: the fibre product
  `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{pr₂, 𝔸^ι, y} Spec K`.
- `AlgebraicGeometry.affineSpacePair.sndFiber.fieldPointsEquiv`: its `L`-rational points.
- `FrobeniusModule.Equiv.trace_frobenius_pow`: isomorphic Frobenius modules have the same
  traces of the powers of the Frobenius.
- `AlgebraicGeometry.WeilComplex.cohomologyFrobeniusModuleEquivOfIso`: isomorphic Weil complexes
  on `Spec k₀` have isomorphic cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section SpecOver

variable (k₀ : Type u) [Field k₀] (K : Type u) [Field K] [Algebra k₀ K]

/-- The scheme `Spec K`, which is a `k₀`-scheme through `Spec K ⟶ Spec k₀` for every
`k₀`-algebra structure on `K`. It is a separate definition, rather than an instance on `Spec K`,
to avoid a diamond with `Spec k₀` over itself. -/
noncomputable def specOver : Scheme.{u} :=
  Spec (.of K)

noncomputable instance : (specOver K).Over (Spec (CommRingCat.of k₀)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap k₀ K))⟩

lemma specOver_over :
    (specOver K ↘ Spec (CommRingCat.of k₀)) = Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) :=
  rfl

/-- The tautological `K`-rational point `𝟙 : Spec K ⟶ Spec K` of `specOver K`. -/
noncomputable def specOver.tautPoint : (specOver K ↘ Spec (CommRingCat.of k₀)).fieldPoints K :=
  ⟨𝟙 _, Category.id_comp _⟩

/-- The `L`-rational points of `Spec K` over `k₀` are the `k₀`-algebra maps `K ⟶ L`. -/
noncomputable def specOver.algHomEquivFieldPoints (L : Type u) [Field L] [Algebra k₀ L] :
    (K →ₐ[k₀] L) ≃ (specOver K ↘ Spec (CommRingCat.of k₀)).fieldPoints L where
  toFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [specOver_over, ← Spec.map_comp]
    congr 1
    ext a
    simp⟩
  invFun x :=
    { toRingHom := (Spec.preimage x.1).hom
      commutes' := fun a ↦ by
        have h : CommRingCat.ofHom (algebraMap k₀ K) ≫ Spec.preimage x.1 =
            CommRingCat.ofHom (algebraMap k₀ L) := by
          apply Spec.map_injective
          rw [Spec.map_comp, Spec.map_preimage]
          exact x.2
        exact congrArg (fun f ↦ f.hom a) h }
  left_inv φ := by
    ext a
    simp [Spec.preimage_map]
  right_inv x := Subtype.ext (Spec.map_preimage x.1)

lemma specOver.algHomEquivFieldPoints_apply_coe (L : Type u) [Field L] [Algebra k₀ L]
    (φ : K →ₐ[k₀] L) :
    (specOver.algHomEquivFieldPoints k₀ K L φ).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  rfl

/-- The `L`-rational point of `Spec K` given by an isomorphism `σ : K ≃ₐ[k₀] L` is the transport
of the tautological point along `σ`. -/
lemma specOver.algHomEquivFieldPoints_eq_fieldPointsCongr (L : Type u) [Field L] [Algebra k₀ L]
    (σ : K ≃ₐ[k₀] L) :
    specOver.algHomEquivFieldPoints k₀ K L σ.toAlgHom =
      (specOver K ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ (specOver.tautPoint k₀ K) :=
  Subtype.ext (Category.comp_id _).symm

/-- There are `n` endomorphisms of the `k₀`-algebra `𝔽_{qⁿ}`, all of them automorphisms. -/
theorem _root_.FiniteField.nat_card_algHom_galoisExtension [Finite k₀] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) = n := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  rw [← Nat.card_congr (algEquivEquivAlgHom k₀ _).toEquiv, IsGalois.card_aut_eq_finrank,
    FiniteField.finrank_galoisExtension k₀ n hn]

/-- A function on the `𝔽_{qⁿ}`-rational points of `Spec 𝔽_{qⁿ}` over `k₀` which is invariant
under the `k₀`-automorphisms of `𝔽_{qⁿ}` sums to `n` times its value at the tautological point:
every point is a Galois conjugate of the tautological one, and there are `n` of them. -/
theorem specOver.finsum_fieldPoints_eq_nsmul [Finite k₀] {n : ℕ} (hn : n ≠ 0) {M : Type*}
    [AddCommMonoid M]
    (f : (specOver (FiniteField.galoisExtension k₀ n) ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n) → M)
    (hf : ∀ (σ : FiniteField.galoisExtension k₀ n ≃ₐ[k₀] FiniteField.galoisExtension k₀ n) x,
      f (Scheme.Hom.fieldPointsCongr _ σ x) = f x) :
    ∑ᶠ x, f x = n • f (specOver.tautPoint k₀ _) := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have h (φ : FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :
      f (specOver.algHomEquivFieldPoints k₀ _ _ φ) = f (specOver.tautPoint k₀ _) := by
    rw [← MulEquiv.apply_symm_apply (algEquivEquivAlgHom k₀ _) φ]
    exact (congrArg f (specOver.algHomEquivFieldPoints_eq_fieldPointsCongr k₀ _ _ _)).trans
      (hf _ _)
  rw [← finsum_comp_equiv (specOver.algHomEquivFieldPoints k₀ _ _)]
  simp_rw [h]
  have : Fintype (FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    FiniteField.nat_card_algHom_galoisExtension k₀ hn]

end SpecOver

section Points

/-- The global section `(Spec φ ≫ g)^* c` of `Spec S`, read in `S`, is the image under `φ` of the
global section `g^* c` of `Spec R`, read in `R`. -/
lemma ΓSpecIso_hom_appTop_specMap_comp {R S : CommRingCat.{u}} (φ : R ⟶ S) {X : Scheme.{u}}
    (g : Spec R ⟶ X) (c : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso S).hom.hom ((Spec.map φ ≫ g).appTop c) =
      φ.hom ((Scheme.ΓSpecIso R).hom.hom (g.appTop c)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

variable (ι : Type u) (k₀ : Type u) [Field k₀] {K L : Type u} [Field K] [Field L] [Algebra k₀ K]
  [Algebra k₀ L]

/-- The identification `𝔸¹(K) ≃ K` is compatible with isomorphisms of the coefficient field. -/
lemma AffineSpace.fieldPointsEquiv_fieldPointsCongr (σ : K ≃ₐ[k₀] L)
    (x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    AffineSpace.fieldPointsEquiv k₀ L (Scheme.Hom.fieldPointsCongr _ σ x) =
      σ (AffineSpace.fieldPointsEquiv k₀ K x) :=
  ΓSpecIso_hom_appTop_specMap_comp _ x.1 _

omit [Algebra k₀ L] in
/-- The coordinate of the product `μ(z) = x y` of the coordinates of a point `z` of the affine
plane. -/
lemma affinePlane.ΓSpecIso_hom_appTop_mul (z : Spec (CommRingCat.of L) ⟶ affinePlane k₀) :
    (Scheme.ΓSpecIso (.of L)).hom.hom
        ((z ≫ affinePlane.mul k₀).appTop (AffineSpace.coord _ PUnit.unit)) =
      (Scheme.ΓSpecIso (.of L)).hom.hom
          ((z ≫ affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit)) *
        (Scheme.ΓSpecIso (.of L)).hom.hom
          ((z ≫ affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affinePlane.mul,
    AffineSpace.homOfVector_appTop_coord, map_mul, map_mul, Scheme.Hom.comp_appTop,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply]

/-- The identification `𝔸^ι(K) ≃ K^ι` is compatible with isomorphisms of the coefficient
field. -/
lemma AffineSpace.fieldPointsEquivPi_fieldPointsCongr (σ : K ≃ₐ[k₀] L)
    (x : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    AffineSpace.fieldPointsEquivPi ι k₀ L (Scheme.Hom.fieldPointsCongr _ σ x) =
      fun i ↦ σ (AffineSpace.fieldPointsEquivPi ι k₀ K x i) :=
  funext fun _ ↦ ΓSpecIso_hom_appTop_specMap_comp _ x.1 _

omit [Algebra k₀ L] in
/-- The coordinate of the pairing `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` of the coordinates of a point `z` of
`𝔸^ι ×_{k₀} 𝔸^ι`. -/
lemma affineSpacePair.ΓSpecIso_hom_appTop_pairing [Fintype ι]
    (z : Spec (CommRingCat.of L) ⟶ affineSpacePair ι k₀) :
    (Scheme.ΓSpecIso (.of L)).hom.hom
        ((z ≫ affineSpacePair.pairing ι k₀).appTop (AffineSpace.coord _ PUnit.unit)) =
      ∑ i, (Scheme.ΓSpecIso (.of L)).hom.hom
          ((z ≫ affineSpacePair.fst ι k₀).appTop (AffineSpace.coord _ i)) *
        (Scheme.ΓSpecIso (.of L)).hom.hom
          ((z ≫ affineSpacePair.snd ι k₀).appTop (AffineSpace.coord _ i)) := by
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineSpacePair.pairing_appTop_coord, map_sum, map_mul]

end Points

section Fibre

variable {ι : Type u} {k₀ : Type u} [Field k₀] {K : Type u} [Field K] [Algebra k₀ K]

/-- A `K`-rational point `y : Spec K ⟶ X` of a `k₀`-scheme, as a morphism of `k₀`-schemes
`specOver K ⟶ X`. -/
noncomputable def specOver.homOfFieldPoint {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) : specOver K ⟶ X :=
  y.1

instance {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    (specOver.homOfFieldPoint y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨y.2⟩

instance [Module.Finite k₀ K] : IsFinite (specOver K ↘ Spec (CommRingCat.of k₀)) := by
  rw [specOver_over, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.2 inferInstance

/-- The fibre product `𝔸² ×_{pr₂, 𝔸¹, y} Spec K` of the second projection of the affine plane
and a `K`-rational point `y` of the affine line, as a `k₀`-scheme through `Spec K`. -/
noncomputable def affinePlane.sndFiber
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints K) : Scheme.{u} :=
  pullback (affinePlane.snd k₀) (specOver.homOfFieldPoint y)

section AffinePlaneFibre

variable (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints K)

noncomputable instance affinePlane.sndFiber.instOver :
    (affinePlane.sndFiber y).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.snd _ _ ≫ specOver K ↘ Spec (CommRingCat.of k₀)⟩

/-- The projection `𝔸² ×_{𝔸¹} Spec K ⟶ 𝔸²`. -/
noncomputable def affinePlane.sndFiber.fst : affinePlane.sndFiber y ⟶ affinePlane k₀ :=
  pullback.fst _ _

/-- The projection `𝔸² ×_{𝔸¹} Spec K ⟶ Spec K`, the base change of `pr₂`. -/
noncomputable def affinePlane.sndFiber.snd : affinePlane.sndFiber y ⟶ specOver K :=
  pullback.snd _ _

lemma affinePlane.sndFiber.isPullback :
    IsPullback (affinePlane.sndFiber.fst y) (affinePlane.sndFiber.snd y) (affinePlane.snd k₀)
      (specOver.homOfFieldPoint y) :=
  IsPullback.of_hasPullback _ _

lemma affinePlane.sndFiber.over :
    (affinePlane.sndFiber y ↘ Spec (CommRingCat.of k₀)) =
      affinePlane.sndFiber.snd y ≫ specOver K ↘ Spec (CommRingCat.of k₀) :=
  rfl

instance affinePlane.sndFiber.isOver_snd :
    (affinePlane.sndFiber.snd y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance affinePlane.sndFiber.isOver_fst :
    (affinePlane.sndFiber.fst y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by
    rw [← comp_over (affinePlane.snd k₀) (Spec (CommRingCat.of k₀)), ← Category.assoc,
      (affinePlane.sndFiber.isPullback y).w, Category.assoc, comp_over]
    rfl⟩

instance affinePlane.sndFiber.isSeparated_snd : IsSeparated (affinePlane.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affinePlane.sndFiber.quasiCompact_snd : QuasiCompact (affinePlane.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affinePlane.sndFiber.locallyOfFiniteType_snd :
    LocallyOfFiniteType (affinePlane.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affinePlane.sndFiber.isSeparated_over [Module.Finite k₀ K] :
    IsSeparated (affinePlane.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (IsSeparated (affinePlane.sndFiber.snd y ≫ _))

instance affinePlane.sndFiber.quasiCompact_over [Module.Finite k₀ K] :
    QuasiCompact (affinePlane.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiCompact (affinePlane.sndFiber.snd y ≫ _))

instance affinePlane.sndFiber.locallyOfFiniteType_over [Module.Finite k₀ K] :
    LocallyOfFiniteType (affinePlane.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (affinePlane.sndFiber.snd y ≫ _))

variable {y} in
/-- The morphism `Spec L ⟶ 𝔸² ×_{𝔸¹} Spec K` given by the point `(x, φ(y))` of `𝔸²` over the
point `φ : Spec L ⟶ Spec K`, for a `k₀`-embedding `φ : K ⟶ L` and `x ∈ L`. -/
noncomputable def affinePlane.sndFiber.lift {L : Type u} [Field L] [Algebra k₀ L]
    (φ : K →ₐ[k₀] L) (x : L) : Spec (CommRingCat.of L) ⟶ affinePlane.sndFiber y :=
  pullback.lift
    (pullback.lift ((AffineSpace.fieldPointsEquiv k₀ L).symm x).1
      ((specOver.algHomEquivFieldPoints k₀ K L φ).1 ≫ y.1) (by
        rw [((AffineSpace.fieldPointsEquiv k₀ L).symm x).2, Category.assoc, y.2]
        exact (specOver.algHomEquivFieldPoints k₀ K L φ).2.symm))
    (specOver.algHomEquivFieldPoints k₀ K L φ).1 (pullback.lift_snd _ _ _)

section Lift

variable {y} {L : Type u} [Field L] [Algebra k₀ L] (φ : K →ₐ[k₀] L) (x : L)

lemma affinePlane.sndFiber.lift_snd :
    affinePlane.sndFiber.lift φ x ≫ affinePlane.sndFiber.snd y =
      (specOver.algHomEquivFieldPoints k₀ K L φ).1 :=
  pullback.lift_snd _ _ _

lemma affinePlane.sndFiber.lift_fst_fst :
    affinePlane.sndFiber.lift φ x ≫ affinePlane.sndFiber.fst y ≫ affinePlane.fst k₀ =
      ((AffineSpace.fieldPointsEquiv k₀ L).symm x).1 := by
  rw [affinePlane.sndFiber.lift, affinePlane.sndFiber.fst, pullback.lift_fst_assoc]
  exact pullback.lift_fst _ _ _

lemma affinePlane.sndFiber.lift_fst_snd :
    affinePlane.sndFiber.lift φ x ≫ affinePlane.sndFiber.fst y ≫ affinePlane.snd k₀ =
      (specOver.algHomEquivFieldPoints k₀ K L φ).1 ≫ y.1 := by
  rw [affinePlane.sndFiber.lift, affinePlane.sndFiber.fst, pullback.lift_fst_assoc]
  exact pullback.lift_snd _ _ _

/-- The product of the coordinates of the point `(x, φ(y))` of the affine plane is `x φ(y)`. -/
lemma affinePlane.sndFiber.ΓSpecIso_hom_appTop_lift_mul :
    (Scheme.ΓSpecIso (.of L)).hom.hom
        ((affinePlane.sndFiber.lift φ x ≫ affinePlane.sndFiber.fst y ≫ affinePlane.mul k₀).appTop
          (AffineSpace.coord _ PUnit.unit)) =
      x * φ (AffineSpace.fieldPointsEquiv k₀ K y) := by
  rw [← Category.assoc, affinePlane.ΓSpecIso_hom_appTop_mul, Category.assoc, Category.assoc,
    affinePlane.sndFiber.lift_fst_fst, affinePlane.sndFiber.lift_fst_snd,
    specOver.algHomEquivFieldPoints_apply_coe, ΓSpecIso_hom_appTop_specMap_comp,
    ← AffineSpace.fieldPointsEquiv_apply, Equiv.apply_symm_apply,
    ← AffineSpace.fieldPointsEquiv_apply]
  rfl

lemma affinePlane.sndFiber.lift_over :
    affinePlane.sndFiber.lift φ x ≫ (affinePlane.sndFiber y ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ L)) := by
  rw [affinePlane.sndFiber.over, ← Category.assoc, affinePlane.sndFiber.lift_snd]
  exact (specOver.algHomEquivFieldPoints k₀ K L φ).2
end Lift

/-- The `L`-rational points of `𝔸² ×_{pr₂, 𝔸¹, y} Spec K` are the pairs `(φ, x)` of a
`k₀`-embedding `φ : K ⟶ L` and an element `x ∈ L`: the point `(x, φ(y))` of `𝔸²` over the
point `φ` of `Spec K`. -/
noncomputable def affinePlane.sndFiber.fieldPointsEquiv (L : Type u) [Field L] [Algebra k₀ L] :
    (K →ₐ[k₀] L) × L ≃ (affinePlane.sndFiber y ↘ Spec (CommRingCat.of k₀)).fieldPoints L where
  toFun p := ⟨affinePlane.sndFiber.lift p.1 p.2, affinePlane.sndFiber.lift_over _ _⟩
  invFun w :=
    ((specOver.algHomEquivFieldPoints k₀ K L).symm
        ⟨w.1 ≫ affinePlane.sndFiber.snd y, (Category.assoc _ _ _).trans w.2⟩,
      AffineSpace.fieldPointsEquiv k₀ L ⟨w.1 ≫ affinePlane.sndFiber.fst y ≫ affinePlane.fst k₀,
        by simpa only [Category.assoc, comp_over] using w.2⟩)
  left_inv p := by
    refine Prod.ext ((Equiv.symm_apply_eq _).2 (Subtype.ext ?_))
      ((Equiv.eq_symm_apply _).1 (Subtype.ext ?_))
    · exact affinePlane.sndFiber.lift_snd _ _
    · exact affinePlane.sndFiber.lift_fst_fst _ _
  right_inv w := by
    refine Subtype.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_)
    · rw [Category.assoc, Category.assoc]
      erw [affinePlane.sndFiber.lift_fst_fst]
      rw [Equiv.symm_apply_apply]
      rfl
    · rw [Category.assoc, Category.assoc]
      erw [affinePlane.sndFiber.lift_fst_snd]
      rw [Equiv.apply_symm_apply]
      exact (Category.assoc _ _ _).trans
        (congrArg (w.1 ≫ ·) (affinePlane.sndFiber.isPullback y).w).symm
    · erw [affinePlane.sndFiber.lift_snd]
      rw [Equiv.apply_symm_apply]
      rfl

end AffinePlaneFibre

/-- The fibre product `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{pr₂, 𝔸^ι, y} Spec K` of the second projection and a
`K`-rational point `y` of `𝔸^ι`, as a `k₀`-scheme through `Spec K`. -/
noncomputable def affineSpacePair.sndFiber
    (y : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    Scheme.{u} :=
  pullback (affineSpacePair.snd ι k₀) (specOver.homOfFieldPoint y)

variable (y : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints K)

noncomputable instance affineSpacePair.sndFiber.instOver :
    (affineSpacePair.sndFiber y).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.snd _ _ ≫ specOver K ↘ Spec (CommRingCat.of k₀)⟩

/-- The projection `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{𝔸^ι} Spec K ⟶ 𝔸^ι ×_{k₀} 𝔸^ι`. -/
noncomputable def affineSpacePair.sndFiber.fst :
    affineSpacePair.sndFiber y ⟶ affineSpacePair ι k₀ :=
  pullback.fst _ _

/-- The projection `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{𝔸^ι} Spec K ⟶ Spec K`, the base change of `pr₂`. -/
noncomputable def affineSpacePair.sndFiber.snd : affineSpacePair.sndFiber y ⟶ specOver K :=
  pullback.snd _ _

lemma affineSpacePair.sndFiber.isPullback :
    IsPullback (affineSpacePair.sndFiber.fst y) (affineSpacePair.sndFiber.snd y)
      (affineSpacePair.snd ι k₀) (specOver.homOfFieldPoint y) :=
  IsPullback.of_hasPullback _ _

lemma affineSpacePair.sndFiber.over :
    (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) =
      affineSpacePair.sndFiber.snd y ≫ specOver K ↘ Spec (CommRingCat.of k₀) :=
  rfl

instance affineSpacePair.sndFiber.isOver_snd :
    (affineSpacePair.sndFiber.snd y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance affineSpacePair.sndFiber.isOver_fst :
    (affineSpacePair.sndFiber.fst y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by
    rw [← comp_over (affineSpacePair.snd ι k₀) (Spec (CommRingCat.of k₀)), ← Category.assoc,
      (affineSpacePair.sndFiber.isPullback y).w, Category.assoc, comp_over]
    rfl⟩

instance affineSpacePair.sndFiber.isSeparated_snd : IsSeparated (affineSpacePair.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.sndFiber.quasiCompact_snd :
    QuasiCompact (affineSpacePair.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.sndFiber.locallyOfFiniteType_snd [Finite ι] :
    LocallyOfFiniteType (affineSpacePair.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.sndFiber.isSeparated_over [Module.Finite k₀ K] :
    IsSeparated (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (IsSeparated (affineSpacePair.sndFiber.snd y ≫ _))

instance affineSpacePair.sndFiber.quasiCompact_over [Module.Finite k₀ K] :
    QuasiCompact (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiCompact (affineSpacePair.sndFiber.snd y ≫ _))

instance affineSpacePair.sndFiber.locallyOfFiniteType_over [Finite ι] [Module.Finite k₀ K] :
    LocallyOfFiniteType (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (affineSpacePair.sndFiber.snd y ≫ _))

variable {y} in
/-- The morphism `Spec L ⟶ (𝔸^ι ×_{k₀} 𝔸^ι) ×_{𝔸^ι} Spec K` given by the point `(x, φ(y))` of
`𝔸^ι ×_{k₀} 𝔸^ι` over the point `φ : Spec L ⟶ Spec K`, for a `k₀`-embedding `φ : K ⟶ L` and
`x ∈ L^ι`. -/
noncomputable def affineSpacePair.sndFiber.lift {L : Type u} [Field L] [Algebra k₀ L]
    (φ : K →ₐ[k₀] L) (x : ι → L) : Spec (CommRingCat.of L) ⟶ affineSpacePair.sndFiber y :=
  pullback.lift
    (pullback.lift ((AffineSpace.fieldPointsEquivPi ι k₀ L).symm x).1
      ((specOver.algHomEquivFieldPoints k₀ K L φ).1 ≫ y.1) (by
        rw [((AffineSpace.fieldPointsEquivPi ι k₀ L).symm x).2, Category.assoc, y.2]
        exact (specOver.algHomEquivFieldPoints k₀ K L φ).2.symm))
    (specOver.algHomEquivFieldPoints k₀ K L φ).1 (pullback.lift_snd _ _ _)

section Lift

variable {y} {L : Type u} [Field L] [Algebra k₀ L] (φ : K →ₐ[k₀] L) (x : ι → L)

lemma affineSpacePair.sndFiber.lift_snd :
    affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.snd y =
      (specOver.algHomEquivFieldPoints k₀ K L φ).1 :=
  pullback.lift_snd _ _ _

lemma affineSpacePair.sndFiber.lift_fst_fst :
    affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.fst y ≫
        affineSpacePair.fst ι k₀ =
      ((AffineSpace.fieldPointsEquivPi ι k₀ L).symm x).1 := by
  rw [affineSpacePair.sndFiber.lift, affineSpacePair.sndFiber.fst, pullback.lift_fst_assoc,
    affineSpacePair.fst, pullback.lift_fst]

lemma affineSpacePair.sndFiber.lift_fst_snd :
    affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.fst y ≫
        affineSpacePair.snd ι k₀ =
      (specOver.algHomEquivFieldPoints k₀ K L φ).1 ≫ y.1 := by
  rw [affineSpacePair.sndFiber.lift, affineSpacePair.sndFiber.fst, pullback.lift_fst_assoc,
    affineSpacePair.snd, pullback.lift_snd]

/-- The pairing of the coordinates of the point `(x, φ(y))` of `𝔸^ι ×_{k₀} 𝔸^ι` is
`∑ᵢ xᵢ φ(yᵢ)`. -/
lemma affineSpacePair.sndFiber.ΓSpecIso_hom_appTop_lift_pairing [Fintype ι] :
    (Scheme.ΓSpecIso (.of L)).hom.hom
        ((affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.fst y ≫
          affineSpacePair.pairing ι k₀).appTop (AffineSpace.coord _ PUnit.unit)) =
      ∑ i, x i * φ (AffineSpace.fieldPointsEquivPi ι k₀ K y i) := by
  rw [← Category.assoc, affineSpacePair.ΓSpecIso_hom_appTop_pairing]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Category.assoc, Category.assoc, affineSpacePair.sndFiber.lift_fst_fst,
    affineSpacePair.sndFiber.lift_fst_snd, specOver.algHomEquivFieldPoints_apply_coe,
    ΓSpecIso_hom_appTop_specMap_comp, ← AffineSpace.fieldPointsEquivPi_apply,
    Equiv.apply_symm_apply, ← AffineSpace.fieldPointsEquivPi_apply]
  rfl

lemma affineSpacePair.sndFiber.lift_over :
    affineSpacePair.sndFiber.lift φ x ≫ (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ L)) := by
  rw [affineSpacePair.sndFiber.over, ← Category.assoc, affineSpacePair.sndFiber.lift_snd]
  exact (specOver.algHomEquivFieldPoints k₀ K L φ).2

end Lift

/-- The `L`-rational points of `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{pr₂, 𝔸^ι, y} Spec K` are the pairs `(φ, x)`
of a `k₀`-embedding `φ : K ⟶ L` and a vector `x ∈ L^ι`: the point `(x, φ(y))` of
`𝔸^ι ×_{k₀} 𝔸^ι` over the point `φ` of `Spec K`. -/
noncomputable def affineSpacePair.sndFiber.fieldPointsEquiv (L : Type u) [Field L]
    [Algebra k₀ L] :
    (K →ₐ[k₀] L) × (ι → L) ≃
      (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)).fieldPoints L where
  toFun p := ⟨affineSpacePair.sndFiber.lift p.1 p.2, affineSpacePair.sndFiber.lift_over _ _⟩
  invFun w :=
    ((specOver.algHomEquivFieldPoints k₀ K L).symm
        ⟨w.1 ≫ affineSpacePair.sndFiber.snd y, (Category.assoc _ _ _).trans w.2⟩,
      AffineSpace.fieldPointsEquivPi ι k₀ L
        ⟨w.1 ≫ affineSpacePair.sndFiber.fst y ≫ affineSpacePair.fst ι k₀,
          by simpa only [Category.assoc, comp_over] using w.2⟩)
  left_inv p := by
    refine Prod.ext ((Equiv.symm_apply_eq _).2 (Subtype.ext ?_))
      ((Equiv.eq_symm_apply _).1 (Subtype.ext ?_))
    · exact affineSpacePair.sndFiber.lift_snd _ _
    · exact affineSpacePair.sndFiber.lift_fst_fst _ _
  right_inv w := by
    refine Subtype.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_)
    · rw [Category.assoc, Category.assoc]
      refine (affineSpacePair.sndFiber.lift_fst_fst _ _).trans ?_
      rw [Equiv.symm_apply_apply]
      rfl
    · rw [Category.assoc, Category.assoc]
      refine (affineSpacePair.sndFiber.lift_fst_snd _ _).trans ?_
      rw [Equiv.apply_symm_apply]
      exact (Category.assoc _ _ _).trans
        (congrArg (w.1 ≫ ·) (affineSpacePair.sndFiber.isPullback y).w).symm
    · refine (affineSpacePair.sndFiber.lift_snd _ _).trans ?_
      rw [Equiv.apply_symm_apply]
      rfl

end Fibre

end AlgebraicGeometry

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- Isomorphic Frobenius modules have the same traces of the powers of the Frobenius. -/
theorem Equiv.trace_frobenius_pow {M N : FrobeniusModule K} (e : M.Equiv N) (m : ℕ) :
    LinearMap.trace K _ (N.frobenius.toLinearMap ^ m) =
      LinearMap.trace K _ (M.frobenius.toLinearMap ^ m) := by
  have h (f : Module.End K M.carrier) : e.toLinearEquiv.conj (f ^ m) =
      (e.toLinearEquiv.conj f) ^ m := by
    induction m with
    | zero => exact e.toLinearEquiv.conj_id
    | succ m ih => rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearEquiv.conj_comp, ih]
  have hN : N.frobenius.toLinearMap = e.toLinearEquiv.conj M.frobenius.toLinearMap :=
    e.frobeniusEnd_eq_conj
  rw [hN, ← h, LinearMap.trace_conj']

end FrobeniusModule

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Isomorphic Weil complexes on `Spec k₀` have isomorphic cohomology, with its Frobenius. -/
noncomputable def cohomologyFrobeniusModuleEquivOfIso
    {M M' : WeilComplex k₀ l (Spec (CommRingCat.of k₀))} (e : M ≅ M') (r : ℤ) :
    (M.cohomologyFrobeniusModule r).Equiv (M'.cohomologyFrobeniusModule r) :=
  WeilSheaf.globalSectionsEquivOfIso ((homologySheaf r).mapIso e)

/-- The direct images with compact support along equal morphisms are isomorphic. -/
theorem nonempty_iso_derivedLowerShriek_of_eq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {f g : X ⟶ Y}
    (h : f = g) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l f ≅ derivedLowerShriek k₀ l g) := by
  subst h
  exact ⟨Iso.refl _⟩

end AlgebraicGeometry.WeilComplex
