/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierTrace
public import WeilConjectures.WeilSheaf.TraceTriangleAdditivity
public import WeilConjectures.ZetaFunction.WeilObjectComparisonOpenClosed

/-!
# The trace function of a direct image with compact support

For a separated quasi-compact morphism `f : X ⟶ Y` locally of finite type of `k₀`-schemes, a
Weil complex `K` on `X`, `n ≥ 1` and `y ∈ Y(𝔽_{qⁿ})`, the trace function of `Rf₀! K` at `y` is
the sum of the trace function of `K` over the `𝔽_{qⁿ}`-rational points of the fibre:

`t_{Rf₀! K, n}(y) = ∑_{x ∈ X(𝔽_{qⁿ}), f(x) = y} t_{K, n}(x)`.

The proof is compact-support base change along `y : Spec 𝔽_{qⁿ} ⟶ Y` and the Grothendieck–Lefschetz
formula on the fibre `X ×_Y Spec 𝔽_{qⁿ}`, whose `𝔽_{qⁿ}`-rational points over a `k₀`-embedding
`σ` of `𝔽_{qⁿ}` are the rational points of `X` over `σ(y)`; the `n` embeddings contribute the
same sum.

As a consequence, for an open immersion `j : U ↪ X` with closed complement `i : Z ↪ X`, the
trace function of `K` splits as `t_K = t_{j_! j^* K} + t_{i_* i^* K}`, where `t_{j_! j^* K}` is
`t_K` on `U(𝔽_{qⁿ})` and `0` on `Z(𝔽_{qⁿ})`, and symmetrically for `t_{i_* i^* K}`.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerShriek`: the trace function of
  `Rf₀! K` at `y` is the sum of `t_K` over the fibre of `f` over `y`.
- `AlgebraicGeometry.WeilComplex.traceFunction_eq_add_openClosed`: `t_K = t_{j_!j^*K} +
  t_{i_*i^*K}`, with
  `AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerShriek_upperStar_mapFieldPoints`,
  `AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerShriek_upperStar_of_notMem_range` and
  `AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerStar_upperStar_mapFieldPoints`,
  `AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerStar_upperStar_of_notMem_range`.

## Blueprint

Parts (3) and (4) of `proposition-function-sheaf-dictionary`, in the framework of Weil complexes
over `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Fibre

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {K : Type u} [Field K] [Algebra k₀ K]

omit [Finite k₀] in
/-- The image of a Galois conjugate rational point is the Galois conjugate of the image. -/
lemma Scheme.Hom.mapFieldPoints_fieldPointsCongr (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] {L : Type u} [Field L] [Algebra k₀ L]
    (σ : K ≃ₐ[k₀] L) (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    φ.mapFieldPoints L ((X ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ x) =
      (Y ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ (φ.mapFieldPoints K x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- The fibre `X ×_{f, Y, y} Spec K` of a morphism `f : X ⟶ Y` of `k₀`-schemes over a `K`-rational
point `y` of `Y`, as a `k₀`-scheme through `Spec K`. -/
noncomputable def Scheme.Hom.fieldPointFiber (f : X ⟶ Y)
    (y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints K) : Scheme.{u} :=
  pullback f (specOver.homOfFieldPoint y)

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  (y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints K)

noncomputable instance Scheme.Hom.fieldPointFiber.instOver :
    (f.fieldPointFiber y).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.snd _ _ ≫ specOver K ↘ Spec (CommRingCat.of k₀)⟩

/-- The projection `X ×_Y Spec K ⟶ X`. -/
noncomputable def Scheme.Hom.fieldPointFiber.fst : f.fieldPointFiber y ⟶ X :=
  pullback.fst _ _

/-- The projection `X ×_Y Spec K ⟶ Spec K`, the base change of `f`. -/
noncomputable def Scheme.Hom.fieldPointFiber.snd : f.fieldPointFiber y ⟶ specOver K :=
  pullback.snd _ _

omit [Finite k₀] [X.Over (Spec (CommRingCat.of k₀))] [f.IsOver (Spec (CommRingCat.of k₀))] in
lemma Scheme.Hom.fieldPointFiber.isPullback :
    IsPullback (fieldPointFiber.fst f y) (fieldPointFiber.snd f y) f
      (specOver.homOfFieldPoint y) :=
  IsPullback.of_hasPullback _ _

instance Scheme.Hom.fieldPointFiber.isOver_snd :
    (fieldPointFiber.snd f y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance Scheme.Hom.fieldPointFiber.isOver_fst :
    (fieldPointFiber.fst f y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by
    rw [← comp_over f (Spec (CommRingCat.of k₀)), ← Category.assoc,
      (fieldPointFiber.isPullback f y).w, Category.assoc, comp_over]
    rfl⟩

instance Scheme.Hom.fieldPointFiber.isSeparated_snd [IsSeparated f] :
    IsSeparated (fieldPointFiber.snd f y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance Scheme.Hom.fieldPointFiber.quasiCompact_snd [QuasiCompact f] :
    QuasiCompact (fieldPointFiber.snd f y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance Scheme.Hom.fieldPointFiber.locallyOfFiniteType_snd [LocallyOfFiniteType f] :
    LocallyOfFiniteType (fieldPointFiber.snd f y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance Scheme.Hom.fieldPointFiber.isSeparated_over [IsSeparated f] [Module.Finite k₀ K] :
    IsSeparated (f.fieldPointFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (IsSeparated (fieldPointFiber.snd f y ≫ _))

instance Scheme.Hom.fieldPointFiber.quasiCompact_over [QuasiCompact f] [Module.Finite k₀ K] :
    QuasiCompact (f.fieldPointFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiCompact (fieldPointFiber.snd f y ≫ _))

instance Scheme.Hom.fieldPointFiber.locallyOfFiniteType_over [LocallyOfFiniteType f]
    [Module.Finite k₀ K] :
    LocallyOfFiniteType (f.fieldPointFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (fieldPointFiber.snd f y ≫ _))

omit [Finite k₀] in
/-- The `L`-rational points of the fibre `X ×_Y Spec K` lying over a given `L`-rational point `p`
of `Spec K` are the `L`-rational points of `X` over the image `y(p)` of `p` in `Y`. -/
noncomputable def Scheme.Hom.fieldPointFiber.fieldPointsEquiv {L : Type u} [Field L]
    [Algebra k₀ L] (p : (specOver K ↘ Spec (CommRingCat.of k₀)).fieldPoints L) :
    {w : (f.fieldPointFiber y ↘ Spec (CommRingCat.of k₀)).fieldPoints L //
        (fieldPointFiber.snd f y).mapFieldPoints L w = p} ≃
      {x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints L //
        f.mapFieldPoints L x = (specOver.homOfFieldPoint y).mapFieldPoints L p} where
  toFun w := ⟨(fieldPointFiber.fst f y).mapFieldPoints L w.1, Subtype.ext <| by
    rw [Scheme.Hom.mapFieldPoints_coe, Scheme.Hom.mapFieldPoints_coe,
      Scheme.Hom.mapFieldPoints_coe, Category.assoc, (fieldPointFiber.isPullback f y).w,
      ← Category.assoc, ← Scheme.Hom.mapFieldPoints_coe, w.2]⟩
  invFun x := ⟨⟨pullback.lift x.1.1 p.1 (by
      rw [← Scheme.Hom.mapFieldPoints_coe, x.2, Scheme.Hom.mapFieldPoints_coe]), by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
      rw [pullback.lift_snd_assoc]
      exact p.2⟩, Subtype.ext (pullback.lift_snd _ _ _)⟩
  left_inv w := Subtype.ext <| Subtype.ext <| pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans (congrArg Subtype.val w.2).symm)
  right_inv x := Subtype.ext <| Subtype.ext (pullback.lift_fst _ _ _)

end Fibre

namespace WeilComplex

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The sum of the trace function of `K` over the fibre of `f` over a rational point is invariant
under the `k₀`-automorphisms of the coefficient field. -/
private lemma finsum_fiber_fieldPointsCongr (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l X) (n : ℕ)
    (σ : FiniteField.galoisExtension k₀ n ≃ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (z : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ∑ᶠ x : {x // f.mapFieldPoints _ x = (Y ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ z},
        K.traceFunction n x.1 =
      ∑ᶠ x : {x // f.mapFieldPoints _ x = z}, K.traceFunction n x.1 := by
  let e : {x // f.mapFieldPoints _ x = z} ≃
      {x // f.mapFieldPoints _ x = (Y ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ z} :=
    ((X ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ).subtypeEquiv fun x ↦ by
      rw [Scheme.Hom.mapFieldPoints_fieldPointsCongr]
      exact ((Y ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ).injective.eq_iff.symm
  rw [← finsum_comp_equiv e]
  exact finsum_congr fun x ↦ traceFunction_fieldPointsCongr K n σ x.1

/-- A sum over a finite type is the sum over the fibres of a map to a finite type. -/
private lemma finsum_eq_finsum_fiber {α β M : Type*} [AddCommMonoid M] [Finite α] [Finite β]
    (g : α → β) (φ : α → M) :
    ∑ᶠ a, φ a = ∑ᶠ b, ∑ᶠ a : {a // g a = b}, φ a.1 := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [finsum_eq_sum_of_fintype]
  exact (Fintype.sum_fiberwise g φ).symm

/-- **The trace function of a direct image with compact support**
(blueprint `proposition-function-sheaf-dictionary`, part (3); blueprint
`corollary-trace-functions-direct-image-compact`): for a separated quasi-compact morphism
`f : X ⟶ Y` locally of finite type of `k₀`-schemes, with `Y` of finite type over `k₀`, a Weil
complex `K` on `X`, `n ≥ 1` and `y ∈ Y(𝔽_{qⁿ})`,

`t_{Rf₀! K, n}(y) = ∑_{x ∈ X(𝔽_{qⁿ}), f(x) = y} t_{K, n}(x)`. -/
theorem traceFunction_derivedLowerShriek (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l X) {n : ℕ} (hn : n ≠ 0)
    (y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((derivedLowerShriek k₀ l f).obj K).traceFunction n y =
      ∑ᶠ x : {x // f.mapFieldPoints _ x = y}, K.traceFunction n x.1 := by
  set L := FiniteField.galoisExtension k₀ n
  have : Finite L := Module.finite_of_finite k₀
  set g := specOver.homOfFieldPoint y
  let F := f.fieldPointFiber y
  let p := Scheme.Hom.fieldPointFiber.snd f y
  let q := Scheme.Hom.fieldPointFiber.fst f y
  have : Finite ((F ↘ Spec (CommRingCat.of k₀)).fieldPoints L) :=
    (F ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints L
  have : Finite ((specOver L ↘ Spec (CommRingCat.of k₀)).fieldPoints L) :=
    (specOver L ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints L
  -- base change of `Rf₀!` along the point `y : Spec 𝔽_{qⁿ} ⟶ Y`
  obtain ⟨e⟩ := nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l) f g p q
    (Scheme.Hom.fieldPointFiber.isPullback f y)
  have he := e.app K
  dsimp only [Functor.comp_obj] at he
  have hτ : g.mapFieldPoints _ (specOver.tautPoint k₀ L) = y :=
    Subtype.ext (Category.id_comp _)
  -- the sum of `t_K` over the fibre of `f` over a rational point
  let h : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints L → PadicAlgCl l :=
    fun z ↦ ∑ᶠ x : {x // f.mapFieldPoints _ x = z}, K.traceFunction n x.1
  have key : n • ((derivedLowerShriek k₀ l f).obj K).traceFunction n y = n • h y := by
    rw [← hτ, ← traceFunction_upperStar, traceFunction_congr he,
      ← specOver.finsum_fieldPoints_eq_nsmul k₀ hn _
        fun σ x ↦ traceFunction_fieldPointsCongr _ n σ x,
      finsum_traceFunction_derivedLowerShriek _ _ hn]
    simp_rw [traceFunction_upperStar]
    rw [finsum_eq_finsum_fiber (p.mapFieldPoints L)]
    have h₁ (t : (specOver L ↘ Spec (CommRingCat.of k₀)).fieldPoints L) :
        ∑ᶠ w : {w // p.mapFieldPoints L w = t}, K.traceFunction n (q.mapFieldPoints L w.1) =
          h (g.mapFieldPoints L t) :=
      finsum_comp_equiv (Scheme.Hom.fieldPointFiber.fieldPointsEquiv f y t)
        (f := fun x ↦ K.traceFunction n x.1)
    refine (finsum_congr h₁).trans ?_
    refine specOver.finsum_fieldPoints_eq_nsmul k₀ hn _ fun σ t ↦ ?_
    rw [Scheme.Hom.mapFieldPoints_fieldPointsCongr]
    exact finsum_fiber_fieldPointsCongr f K n σ _
  rw [nsmul_eq_mul, nsmul_eq_mul] at key
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) key

/-- The trace function of the direct image with compact support along a monomorphism `φ` at the
image `φ(u)` of a rational point is that of the complex at `u`. -/
theorem traceFunction_derivedLowerShriek_mapFieldPoints (φ : X ⟶ Y) [Mono φ]
    [φ.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated φ] [LocallyOfFiniteType φ] [QuasiCompact φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l X) {n : ℕ} (hn : n ≠ 0)
    (u : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((derivedLowerShriek k₀ l φ).obj K).traceFunction n (φ.mapFieldPoints _ u) =
      K.traceFunction n u := by
  have : Unique {u' // φ.mapFieldPoints _ u' = φ.mapFieldPoints _ u} :=
    ⟨⟨u, rfl⟩, fun v ↦ Subtype.ext (Scheme.Hom.mapFieldPoints_injective φ v.2)⟩
  rw [traceFunction_derivedLowerShriek φ K hn, finsum_unique,
    Unique.default_eq (⟨u, rfl⟩ : {u' // φ.mapFieldPoints _ u' = φ.mapFieldPoints _ u})]

/-- The trace function of the direct image with compact support vanishes at a rational point
outside the image of the rational points. -/
theorem traceFunction_derivedLowerShriek_of_notMem_range (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated φ] [LocallyOfFiniteType φ] [QuasiCompact φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l X) {n : ℕ} (hn : n ≠ 0)
    (y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n))
    (hy : y ∉ Set.range (φ.mapFieldPoints _)) :
    ((derivedLowerShriek k₀ l φ).obj K).traceFunction n y = 0 := by
  have : IsEmpty {u // φ.mapFieldPoints _ u = y} := ⟨fun u ↦ hy ⟨u.1, u.2⟩⟩
  rw [traceFunction_derivedLowerShriek φ K hn, finsum_of_isEmpty]

section OpenClosed

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- **The open–closed decomposition of the trace function** (blueprint
`proposition-function-sheaf-dictionary`, part (4)): for an open immersion `j : U ↪ X` with
closed complement `i : Z ↪ X` and a Weil complex `K` on `X`,
`t_{K, n} = t_{j_! j^* K, n} + t_{i_* i^* K, n}`. -/
theorem traceFunction_eq_add_openClosed (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (K : WeilComplex k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    K.traceFunction n x =
      ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)).traceFunction n x +
        ((derivedLowerStar i).obj ((upperStar i).obj K)).traceFunction n x := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_distTriang_openClosed (k₀ := k₀) j i hij K
  rw [← traceFunction_congr e₁, ← traceFunction_congr e₂, ← traceFunction_congr e₃]
  exact traceFunction_eq_add_of_distTriang T hT n x

/-- The trace function of `j_! j^* K` at a rational point of `U` is that of `K`
(blueprint `proposition-function-sheaf-dictionary`, part (4)). -/
theorem traceFunction_derivedLowerShriek_upperStar_mapFieldPoints (K : WeilComplex k₀ l X)
    {n : ℕ} (hn : n ≠ 0)
    (u : (U ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)).traceFunction n
        (j.mapFieldPoints _ u) =
      K.traceFunction n (j.mapFieldPoints _ u) := by
  rw [traceFunction_derivedLowerShriek_mapFieldPoints j _ hn, traceFunction_upperStar]

/-- The trace function of `j_! j^* K` vanishes at the rational points of `X` outside `U`
(blueprint `proposition-function-sheaf-dictionary`, part (4)). -/
theorem traceFunction_derivedLowerShriek_upperStar_of_notMem_range (K : WeilComplex k₀ l X)
    {n : ℕ} (hn : n ≠ 0)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n))
    (hx : x ∉ Set.range (j.mapFieldPoints _)) :
    ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj K)).traceFunction n x = 0 :=
  traceFunction_derivedLowerShriek_of_notMem_range j _ hn x hx

/-- The trace function of `i_* i^* K` at a rational point of `Z` is that of `K`
(blueprint `proposition-function-sheaf-dictionary`, part (4)). -/
theorem traceFunction_derivedLowerStar_upperStar_mapFieldPoints (K : WeilComplex k₀ l X)
    {n : ℕ} (hn : n ≠ 0)
    (z : (Z ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((derivedLowerStar i).obj ((upperStar i).obj K)).traceFunction n (i.mapFieldPoints _ z) =
      K.traceFunction n (i.mapFieldPoints _ z) := by
  rw [← traceFunction_congr (derivedLowerShriekObjIsoDerivedLowerStar i _),
    traceFunction_derivedLowerShriek_mapFieldPoints i _ hn, traceFunction_upperStar]

/-- The trace function of `i_* i^* K` vanishes at the rational points of `X` outside `Z`
(blueprint `proposition-function-sheaf-dictionary`, part (4)). -/
theorem traceFunction_derivedLowerStar_upperStar_of_notMem_range (K : WeilComplex k₀ l X)
    {n : ℕ} (hn : n ≠ 0)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n))
    (hx : x ∉ Set.range (i.mapFieldPoints _)) :
    ((derivedLowerStar i).obj ((upperStar i).obj K)).traceFunction n x = 0 := by
  rw [← traceFunction_congr (derivedLowerShriekObjIsoDerivedLowerStar i _)]
  exact traceFunction_derivedLowerShriek_of_notMem_range i _ hn x hx

end OpenClosed

end WeilComplex

end AlgebraicGeometry
