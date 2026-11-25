/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSpace
public import WeilConjectures.TraceFormula.ShriekTraceFunctionAffineLine
public import WeilConjectures.TraceFormula.ShriekTraceFunctionInduction

/-!

# The base cases of the sheaf–function compatibility of the Weil lower shriek

By Noetherian induction (`ProEtale.CondensedRing.weilShriekTraceFunction_of_genericallyHolds`),
the sheaf–function compatibility `ProEtale.CondensedRing.ShriekTraceFunctionAt` of the Weil lower
shriek holds along every morphism as soon as it holds generically
(`ProEtale.CondensedRing.ShriekTraceFunctionGenericallyHolds`). This file reduces the generic
statement to three base cases, stated as separate inputs:

- **dimension zero** (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isFinite_of_etale`, proved in
  `WeilConjectures.TraceFormula.ShriekTraceFunctionFiniteEtale`): `f`
  finite étale. Then `Rf_! = f_*` and the stalk of `f_* K` at `ȳ` is `⊕_{x̄ ↦ ȳ} K_x̄`, on which
  the Frobenius permutes the summands; only the summands at points of degree `n + 1` contribute
  to the trace;
- **the affine line** (`ProEtale.CondensedRing.shriekTraceFunctionAt_overProdMap_polyAffineProj`,
  proved in `WeilConjectures.TraceFormula.ShriekTraceFunctionAffineLine`): the coordinate
  projections `𝔸^{j+1}_k ×_k E ⟶ 𝔸ʲ_k ×_k E`. The relative affine line is open in the relative
  projective line, whose geometric fibres are `ℙ¹_{k̄}`, where the trace formula is the
  Lefschetz–Verdier formula for the Frobenius graph on a proper smooth curve. The case of a
  general smooth morphism of relative dimension one
  (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_smoothOfRelativeDimension_one`) is a
  consequence of the full compatibility (`WeilConjectures.TraceFormula.Statement`);
- **closed immersions**
  (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isClosedImmersion`): `Ri_! = i_*`, whose
  stalk at `ȳ` is `K_ȳ` if `ȳ` lies on the closed subscheme and `0` otherwise.

The closed-immersion case cannot be avoided: every morphism built from finite étale morphisms
and relative affine lines by composition (`shriekTraceFunctionAt_comp`)
and open–closed dévissage of the source (`shriekTraceFunctionAt_of_isCompl`) satisfies
`dim 𝒪_{X,x} ≥ dim 𝒪_{Y,f(x)}`, which fails for a closed point of the affine line.

## The reduction

The reduction (`ProEtale.CondensedRing.shriekTraceFunctionGenericallyHolds_of_baseCases`) goes
through the generic quotient of `X` by its automorphism `e_X` of finite order
(`AlgebraicGeometry.exists_isFinite_etale_of_pow_eq_refl`): there are a nonempty
`e_X`-stable open `U ⊆ X`, its reduction `Z`, and a finite étale morphism `π : Z ⟶ V` to an
affine scheme `V`, invariant under `e_Z`. The compatibility along `U ⟶ Y` follows from the one
along `Z ⟶ Y` by dévissage (`U = ∅ ⊔ Z`), and `Z ⟶ Y` factors as the chain
```
Z ⟶ Z ×_k E ⟶ V ×_k E ⟶ 𝔸ᴺ_k ×_k E ⟶ 𝔸ᴺ⁻¹_k ×_k E ⟶ ⋯ ⟶ 𝔸⁰_k ×_k E ⟶ E ⟶ Y
```
of the graph of `Z ⟶ E` (a closed immersion), `π ×_k E` (finite étale), a closed embedding of
`V` into `𝔸ᴺ_k`, the coordinate projections (relative affine lines), an isomorphism,
and the closed immersion of the fixed locus `E` of `e_Y^{m+1}`, through which `Z ⟶ Y` factors.
The automorphisms of the intermediate schemes are the products of `e_Z`, the identity and `e_E`;
they have finite order, so that `shriekTraceFunctionAt_comp` composes the base cases.

The closed-immersion case is proved here from the dimension-zero case (for the identity of `X`)
and compactly supported base change of Weil objects
(`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUpperStar_weilLowerShriek`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### The open complement of a stable closed immersion -/

section Complement

variable {S : Scheme.{u}}

/-- If `a ≫ f = f ≫ b'` with `b ≫ b' = 𝟙`, then `b` preserves the complement of the image of
`f`. -/
lemma notMem_range_of_comp_eq {X Y : Over S} (f : X ⟶ Y) {a : X ⟶ X} {b b' : Y ⟶ Y}
    (hb : b ≫ b' = 𝟙 Y) (h : a ≫ f = f ≫ b') {y : Y.left} (hy : y ∉ Set.range f.left.base) :
    b.left.base y ∉ Set.range f.left.base := by
  rintro ⟨x, hx⟩
  refine hy ⟨a.left.base x, ?_⟩
  have h₁ : f.left.base (a.left.base x) = b'.left.base (f.left.base x) := congr(($h).left.base x)
  have h₂ : b'.left.base (b.left.base y) = y := congr(($hb).left.base y)
  rw [h₁, hx, h₂]

/-- The open complement `V` of a closed immersion `f : X ⟶ Y` stable under automorphisms
`e_X`, `e_Y`, as a scheme over `S` with the restriction `e_V` of `e_Y`. -/
lemma exists_isOpenImmersion_range_eq_compl {X Y : Over S} [IsLocallyNoetherian Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (eX : X ≅ X)
    (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom) [IsClosedImmersion f.left] :
    ∃ (V : Over S) (_ : LocallyOfFiniteType V.hom) (_ : QuasiCompact V.hom)
      (_ : IsSeparated V.hom) (eV : V ≅ V) (j : V ⟶ Y) (_ : IsOpenImmersion j.left)
      (_ : eV.hom ≫ j = j ≫ eY.hom), Set.range j.left.base = (Set.range f.left.base)ᶜ := by
  have hinv : eX.inv ≫ f = f ≫ eY.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% hf, Iso.hom_inv_id, Category.comp_id]
  let U : Y.left.Opens :=
    ⟨(Set.range f.left.base)ᶜ, f.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU₁ : U ≤ eY.hom.left ⁻¹ᵁ U := fun z hz ↦ notMem_range_of_comp_eq f eY.hom_inv_id hinv hz
  have hU₂ : U ≤ eY.inv.left ⁻¹ᵁ U := fun z hz ↦ notMem_range_of_comp_eq f eY.inv_hom_id hf hz
  refine ⟨Over.mk (U.ι ≫ Y.hom), inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Y.hom)),
    inferInstanceAs (QuasiCompact (U.ι ≫ Y.hom)), inferInstanceAs (IsSeparated (U.ι ≫ Y.hom)),
    Over.isoMk ⟨eY.hom.left.resLE U U hU₁, eY.inv.left.resLE U U hU₂, ?_, ?_⟩ ?_,
    Over.homMk U.ι rfl, inferInstanceAs (IsOpenImmersion U.ι), ?_, ?_⟩
  · simp [← cancel_mono U.ι, ← Over.comp_left]
  · simp [← cancel_mono U.ι, ← Over.comp_left]
  · simp
  · ext1
    simp
  · exact U.range_ι

end Complement

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The base cases -/

/-- The sheaf–function compatibility holds along every finite étale morphism `f` (for `e_X` of
finite order). -/
def ShriekTraceFunctionFiniteEtale : Prop :=
  ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
    [IsFinite f.left] → [Etale f.left] → (∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) →
    ShriekTraceFunctionAt ℓ eX eY hf

/-- The sheaf–function compatibility holds along every coordinate projection
`𝔸^{j+1}_k ×_k E ⟶ 𝔸ʲ_k ×_k E`, the relative affine line over `𝔸ʲ_k ×_k E`, for the
automorphisms `𝟙 ×_k e_E` with `e_E` of finite order. -/
def ShriekTraceFunctionAffineLine : Prop :=
  ∀ (j : ℕ) (E : Over (Spec (.of k))) [LocallyOfFiniteType E.hom] [QuasiCompact E.hom]
    [IsSeparated E.hom] (eE : E ≅ E), (∃ m : ℕ, eE.pow (m + 1) = Iso.refl E) →
    ShriekTraceFunctionAt ℓ (overProdIso (Iso.refl (polyAffine k (j + 1))) eE)
      (overProdIso (Iso.refl (polyAffine k j)) eE) (overProdIso_refl_hom_comp_overProdMap
        (polyAffineProj k j) eE)

/-- The sheaf–function compatibility holds along every closed immersion `f` (for `e_X` of finite
order). -/
def ShriekTraceFunctionClosedImmersion : Prop :=
  ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
    [IsClosedImmersion f.left] → (∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) →
    ShriekTraceFunctionAt ℓ eX eY hf

/-- **Dimension zero**: the sheaf–function compatibility holds along a finite
étale morphism `f`. The stalk of `Rf_! K = f_* K` at `ȳ` is the sum of the stalks `K_x̄` over
the geometric points `x̄ ↦ ȳ`, permuted by the Frobenius; the trace only sees the summands at
the points fixed by the Frobenius, which are the points of degree `n + 1`
(`ShriekTraceFunctionAt.of_isFinite_of_etale`, which does not need `e_X` to have finite order).
The hypothesis `_he` is therefore redundant; it is kept so that the statement has the form of the
base case `H₀` of `shriekTraceFunctionGenericallyHolds_of_baseCases`. -/
theorem shriekTraceFunctionAt_of_isFinite_of_etale {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [IsFinite f.left] [Etale f.left] (_he : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf :=
  ShriekTraceFunctionAt.of_isFinite_of_etale ℓ eX eY hf

/-- **Closed immersions**: the sheaf–function compatibility holds along a closed
immersion `i : X ⟶ Y`. For a point `ȳ` of `Y` of degree `n + 1`: if `ȳ = x̄ ≫ i`, then
`t(Ri_! K; ȳ) = t(Li^* Ri_! K; x̄)` by the stalks of pullbacks
(`ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUpperStar`), `= t(R𝟙_! L𝟙^* K; x̄)` by
compactly supported base change along the cartesian square `(𝟙, 𝟙, i, i)` (`i` is a
monomorphism), and
`= t(K; x̄)` by the dimension-zero case for `𝟙_X`; the sum on the right has the single term `x̄`.
Otherwise `ȳ` lies on the open complement `V`, and
`Lj^* Ri_! K = 0` by base change along the empty square `V ×_Y X = ∅`. -/
theorem shriekTraceFunctionAt_of_isClosedImmersion {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [IsClosedImmersion f.left] (he : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf := by
  intro K n y
  by_cases hy : y.1.base default ∈ Set.range f.left.base
  · -- `ȳ = x̄ ≫ f`: base change along the cartesian square `(𝟙, 𝟙, f, f)`
    have : Mono f := Over.mono_of_mono_left f
    have hsub : f.left.ker ≤ y.1.ker := by
      rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support, Scheme.Hom.support_ker,
        f.left.isClosedMap.isClosed_range.closure_eq]
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    obtain ⟨v, rfl⟩ := exists_frobeniusFixedPointsMap_eq eY hf y
      (IsClosedImmersion.lift f.left y.1 hsub) (IsClosedImmersion.lift_fac _ _ _)
    have hid : eX.hom ≫ 𝟙 X = 𝟙 X ≫ eX.hom := by simp
    have : IsFinite (𝟙 X : X ⟶ X).left := by rw [Over.id_left]; infer_instance
    have : Etale (𝟙 X : X ⟶ X).left := by rw [Over.id_left]; infer_instance
    rw [← weilStalkTraceAlternatingSum_weilUpperStar ℓ eY eX hf,
      weilStalkTraceAlternatingSum_weilUpperStar_weilLowerShriek ℓ ((mono_iff_isPullback f).1 ‹_›)
          hid
        hid hf hf,
      shriekTraceFunctionAt_of_isFinite_of_etale ℓ k eX eX hid he _ n v]
    have hv : frobeniusFixedPointsMap eX eX hid n v = v :=
      Subtype.ext (by simp [frobeniusFixedPointsMap])
    refine (finsum_eq_single _ ⟨v, by simp⟩ fun x hx ↦
        (hx (by exact Subtype.ext (Subtype.ext (by simpa using x.2)))).elim).trans
      ((finsum_eq_single _ ⟨v, rfl⟩ fun x hx ↦
        (hx (by exact Subtype.ext (Subtype.ext ((cancel_mono f.left).1 x.2)))).elim).trans
        ?_).symm
    rw [weilStalkTraceAlternatingSum_weilUpperStar ℓ eX eX hid K n v, hv]
  · -- `ȳ` on the open complement `V`: base change along the empty square `∅ = V ×_Y X`
    have : IsEmpty {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1} :=
      ⟨fun x ↦ hy ⟨x.1.1.base default, by
        have h := congrArg (fun g ↦ g.base default) x.2; exact h⟩⟩
    rw [finsum_of_isEmpty]
    have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    obtain ⟨V, _, _, _, eV, j, _, hj, hrange⟩ :=
      exists_isOpenImmersion_range_eq_compl eX eY f hf
    have hyV : y.1.base default ∈ Set.range j.left.base := hrange ▸ hy
    have hsub : Set.range y.1.base ⊆ Set.range j.left.base := by
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    obtain ⟨v, rfl⟩ := exists_frobeniusFixedPointsMap_eq eY hj y
      (IsOpenImmersion.lift j.left y.1 hsub) (IsOpenImmersion.lift_fac _ _ _)
    have h₀ : (Iso.refl emptyOver).hom ≫ emptyOverTo X = emptyOverTo X ≫ eX.hom :=
      emptyOverTo_ext _ _
    have h₀' : (Iso.refl emptyOver).hom ≫ emptyOverTo V = emptyOverTo V ≫ eV.hom :=
      emptyOverTo_ext _ _
    rw [← weilStalkTraceAlternatingSum_weilUpperStar ℓ eY eV hj,
      weilStalkTraceAlternatingSum_weilUpperStar_weilLowerShriek ℓ
        (isPullback_emptyOverTo f j (hrange ▸ disjoint_compl_right)) h₀ h₀' hf hj,
      shriekTraceFunctionAt_of_isEmpty ℓ (Iso.refl _) eV h₀' _ n v]
    exact finsum_eq_zero_of_forall_eq_zero fun x ↦ isEmptyElim (x.1.1.base default)

variable {ℓ k}

/-! ### The chain -/

section Chain

variable (H₀ : ShriekTraceFunctionFiniteEtale ℓ k) (H₁ : ShriekTraceFunctionAffineLine ℓ k)
  (H₂ : ShriekTraceFunctionClosedImmersion ℓ k)

section Projections

variable {E Y : Over (Spec (.of k))} [LocallyOfFiniteType E.hom] [QuasiCompact E.hom]
  [IsSeparated E.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {eE : E ≅ E} {eY : Y ≅ Y} {m : ℕ} (heE : eE.pow (m + 1) = Iso.refl E) {ι : E ⟶ Y}
  (hι : eE.hom ≫ ι = ι ≫ eY.hom)

include H₀ H₁ heE in
/-- The compatibility along the projection `𝔸ʲ_k ×_k E ⟶ E` followed by `ι : E ⟶ Y`, from the
one along `ι`: the projection is the composite of the coordinate projections, the relative affine
lines of `ShriekTraceFunctionAffineLine`, and of the isomorphism `𝔸⁰_k ×_k E ≅ E`. -/
lemma shriekTraceFunctionAt_overProdSnd_polyAffine
    (Hι : ShriekTraceFunctionAt ℓ eE eY hι) (j : ℕ) :
    ShriekTraceFunctionAt ℓ (overProdIso (Iso.refl (polyAffine k j)) eE) eY
      (comp_comm_of_comp_comm _ eY eE (by simp) hι :
        (overProdIso (Iso.refl (polyAffine k j)) eE).hom ≫ overProdSnd _ E ≫ ι =
          (overProdSnd _ E ≫ ι) ≫ eY.hom) := by
  have hfin : ∀ j, ((overProdIso (Iso.refl (polyAffine k j)) eE).pow (m + 1)) = Iso.refl _ :=
    fun j ↦ by rw [overProdIso_pow, heE, Iso.pow_refl, overProdIso_refl]
  induction j with
  | zero =>
    exact shriekTraceFunctionAt_comp ℓ _ eY eE (by simp) hι ⟨m, hfin 0⟩ ⟨m, heE⟩
      (H₀ _ _ _ _ _ _ ⟨m, hfin 0⟩) Hι
  | succ j ih =>
    have hp := overProdIso_refl_hom_comp_overProdMap (polyAffineProj k j) eE
    refine ShriekTraceFunctionAt.of_eq ℓ (by simp)
      (shriekTraceFunctionAt_comp ℓ _ eY _ hp _ ⟨m, hfin (j + 1)⟩ ⟨m, hfin j⟩
        (H₁ j E eE ⟨m, heE⟩) ih)

end Projections

include H₀ H₁ H₂ in
/-- The chain `Z ⟶ Z ×_k E ⟶ V ×_k E ⟶ 𝔸ᴺ_k ×_k E ⟶ E ⟶ Y`, for a factorization of `g` through
a closed immersion `ι : E ⟶ Y` with an automorphism `e_E` of finite order and a finite étale
morphism `π : Z ⟶ V` to an affine scheme with `e_Z ≫ π = π`. -/
lemma shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq_aux
    {Z Y V E : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [IsAffine V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
    (eZ : Z ≅ Z) (eY : Y ≅ Y) (eE : E ≅ E) {g : Z ⟶ Y} (hg : eZ.hom ≫ g = g ≫ eY.hom) {m : ℕ}
    (heZ : eZ.pow (m + 1) = Iso.refl Z) (heE : eE.pow (m + 1) = Iso.refl E) (π : Z ⟶ V)
    [IsFinite π.left] [Etale π.left] (hπ : eZ.hom ≫ π = π) (ι : E ⟶ Y)
    [IsClosedImmersion ι.left] (hι : eE.hom ≫ ι = ι ≫ eY.hom) (gE : Z ⟶ E)
    (hgE : eZ.hom ≫ gE = gE ≫ eE.hom) (hgE' : gE ≫ ι = g) :
    ShriekTraceFunctionAt ℓ eZ eY hg := by
  -- a closed embedding of `V` into an affine space
  obtain ⟨N, ιV, _⟩ := exists_isClosedImmersion_polyAffine V
  have hfin : ∀ {W : Over (Spec (.of k))} (eW : W ≅ W), eW.pow (m + 1) = Iso.refl W →
      (overProdIso eW eE).pow (m + 1) = Iso.refl _ :=
    fun eW h ↦ by rw [overProdIso_pow, h, heE, overProdIso_refl]
  have hfinV := hfin (Iso.refl V) (Iso.pow_refl _)
  have hfinN := hfin (Iso.refl (polyAffine k N)) (Iso.pow_refl _)
  have hfinZ := hfin eZ heZ
  -- the compatibility along `E ⟶ Y` and along `𝔸ᴺ_k ×_k E ⟶ E ⟶ Y`
  have HN := shriekTraceFunctionAt_overProdSnd_polyAffine H₀ H₁ heE hι
    (H₂ _ _ _ _ _ hι ⟨m, heE⟩) N
  -- `V ×_k E ⟶ 𝔸ᴺ_k ×_k E`
  have h₃ : (overProdIso (Iso.refl V) eE).hom ≫ overProdMap ιV (𝟙 E) =
      overProdMap ιV (𝟙 E) ≫ (overProdIso (Iso.refl (polyAffine k N)) eE).hom := by
    simp only [overProdIso_hom, Iso.refl_hom, ← overProdMap_comp, Category.id_comp,
      Category.comp_id]
  have H₃ := shriekTraceFunctionAt_comp ℓ _ eY _ h₃ _ ⟨m, hfinV⟩ ⟨m, hfinN⟩
    (H₂ _ _ _ _ _ h₃ ⟨m, hfinV⟩) HN
  -- `Z ×_k E ⟶ V ×_k E`
  have h₂ : (overProdIso eZ eE).hom ≫ overProdMap π (𝟙 E) =
      overProdMap π (𝟙 E) ≫ (overProdIso (Iso.refl V) eE).hom := by
    simp only [overProdIso_hom, Iso.refl_hom, ← overProdMap_comp, Category.id_comp,
      Category.comp_id, hπ]
  have H₂' := shriekTraceFunctionAt_comp ℓ _ eY _ h₂ _ ⟨m, hfinZ⟩ ⟨m, hfinV⟩
    (H₀ _ _ _ _ _ h₂ ⟨m, hfinZ⟩) H₃
  -- the graph `Z ⟶ Z ×_k E`
  have h₁ : eZ.hom ≫ overGraph gE = overGraph gE ≫ (overProdIso eZ eE).hom :=
    (overGraph_overProdMap _ _ hgE.symm).symm
  have H₁' := shriekTraceFunctionAt_comp ℓ _ eY _ h₁ _ ⟨m, heZ⟩ ⟨m, hfinZ⟩
    (H₂ _ _ _ _ _ h₁ ⟨m, heZ⟩) H₂'
  refine ShriekTraceFunctionAt.of_eq ℓ ?_ H₁'
  simp [hgE']

include H₀ H₁ H₂ in
/-- **The chain**: the compatibility along `g : Z ⟶ Y`, if `Z` has a finite étale morphism
`π : Z ⟶ V` to an affine scheme, invariant under `e_Z` of finite order. The morphism `g` factors
through the fixed locus of `e_Y^{m+1}`. -/
theorem shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq
    {Z Y V : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [IsAffine V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (eZ : Z ≅ Z) (eY : Y ≅ Y) {g : Z ⟶ Y} (hg : eZ.hom ≫ g = g ≫ eY.hom) {m : ℕ}
    (heZ : eZ.pow (m + 1) = Iso.refl Z) (π : Z ⟶ V) [IsFinite π.left] [Etale π.left]
    (hπ : eZ.hom ≫ π = π) :
    ShriekTraceFunctionAt ℓ eZ eY hg := by
  have hgm : g ≫ 𝟙 Y = g ≫ (eY.pow (m + 1)).hom := by
    rw [Category.comp_id, ← Iso.pow_hom_comp_eq_comp_pow_hom eZ eY hg m, heZ,
      Iso.refl_hom, Category.id_comp]
  have hc := (Iso.pow_hom_comp_eq_comp_pow_hom eY eY rfl m).symm
  refine shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq_aux H₀ H₁ H₂ eZ eY
    (fixedLocusIso (eY.pow (m + 1)).hom eY hc) hg heZ (fixedLocusIso_pow eY m) π hπ _
    (fixedLocusIso_hom_ι _ eY hc) (equalizer.lift g hgm) (equalizer.hom_ext ?_)
    (equalizer.lift_ι _ _)
  simp [hg]

end Chain

/-! ### The reduction -/

variable (ℓ k) in
/-- **Generic structure**: the three base cases give the sheaf–function compatibility
generically. A nonempty `X` with an automorphism `e_X` of finite order has a nonempty
`e_X`-stable open `U` whose reduction `Z` is finite étale over an affine scheme `V`, invariantly
under `e_Z` (the generic quotient by `e_X`); the compatibility along `U ⟶ Y` follows from the one
along `Z ⟶ Y` by dévissage, and `Z ⟶ Y` is a composite of base cases
(`shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq`). -/
theorem shriekTraceFunctionGenericallyHolds_of_baseCases
    (H₀ : ShriekTraceFunctionFiniteEtale ℓ k) (H₁ : ShriekTraceFunctionAffineLine ℓ k)
    (H₂ : ShriekTraceFunctionClosedImmersion ℓ k) :
    ShriekTraceFunctionGenericallyHolds ℓ k := by
  intro X Y _ _ _ _ _ _ eX eY f hf ⟨m, hm⟩ hX
  obtain ⟨U, _, _, _, eU, j, _, hj, Z, _, _, _, eZ, i, _, hi, V, _, _, π, _, _, hU, hsurj, hπ⟩ :=
    exists_isFinite_etale_of_pow_eq_refl X eX hm
  refine ⟨U, inferInstance, inferInstance, inferInstance, eU, j, inferInstance, hj, hU, ?_⟩
  have heU : eU.pow (m + 1) = Iso.refl U := by
    ext1
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono j.left, ← Over.comp_left,
      Iso.pow_hom_comp_eq_comp_pow_hom eU eX hj m, hm]
    simp
  have heZ : eZ.pow (m + 1) = Iso.refl Z := by
    ext1
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono i.left, ← Over.comp_left,
      Iso.pow_hom_comp_eq_comp_pow_hom eZ eU hi m, heU]
    simp
  have h₀ : (Iso.refl emptyOver).hom ≫ emptyOverTo U = emptyOverTo U ≫ eU.hom :=
    emptyOverTo_ext _ _
  refine shriekTraceFunctionAt_of_isCompl ℓ eU eY (Iso.refl _) eZ _ h₀ hi ?_ ⟨m, heU⟩
    (shriekTraceFunctionAt_of_isEmpty ℓ _ eY _)
    (shriekTraceFunctionAt_of_isFinite_of_etale_of_comp_eq H₀ H₁ H₂ eZ eY _ heZ π hπ)
  rw [hsurj.range_eq, Set.range_eq_empty]
  exact isCompl_bot_top

variable (ℓ k) in
/-- The sheaf–function compatibility holds generically, from the three base cases. -/
theorem shriekTraceFunctionGenericallyHolds : ShriekTraceFunctionGenericallyHolds ℓ k :=
  shriekTraceFunctionGenericallyHolds_of_baseCases ℓ k
    (fun _ _ _ _ _ _ _ _ eX eY _ hf _ _ he ↦
      shriekTraceFunctionAt_of_isFinite_of_etale ℓ k eX eY hf he)
    (fun j E _ _ _ eE he ↦ shriekTraceFunctionAt_overProdMap_polyAffineProj ℓ j E eE he)
    (fun _ _ _ _ _ _ _ _ eX eY _ hf _ he ↦
      shriekTraceFunctionAt_of_isClosedImmersion ℓ k eX eY hf he)

end AlgebraicGeometry.ProEtale.CondensedRing
