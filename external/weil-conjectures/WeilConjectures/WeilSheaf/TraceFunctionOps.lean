/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.TraceFunctionCongr

/-!
# Trace functions of Weil complexes under the operations

The trace function `t_K` of a Weil complex (`AlgebraicGeometry.WeilComplex.traceFunction`) is
compatible with the elementary operations: a shift `[a]` multiplies it by `(-1)ᵃ`, a pullback
`φ^*` composes it with `φ` on rational points, it is invariant under the Galois action on the
coefficient field of the rational points.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_shift`: `t_{K[a]} = (-1)ᵃ t_K`.
- `AlgebraicGeometry.WeilComplex.traceFunction_upperStar`: `t_{φ^* K}(x) = t_K(φ(x))`.
- `AlgebraicGeometry.WeilComplex.traceFunction_fieldPointsCongr`: `t_K(σ(x)) = t_K(x)` for a
  `k₀`-automorphism `σ` of the coefficient field.

## Blueprint

These are the properties of the trace function (blueprint `definition-trace-function`,
`definition-trace-function`) used in the proof of the Fourier trace formula
(sketch blueprint `sec-The-Plancherel-formula`).
-/

@[expose] public section

universe u v

open CategoryTheory Limits

open scoped AlgebraicGeometry.ProEtale

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- Isomorphic Frobenius modules have the same trace of the Frobenius. -/
theorem Equiv.trace_frobeniusEnd {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    LinearMap.trace K _ N.frobeniusEnd = LinearMap.trace K _ M.frobeniusEnd := by
  rw [LinearMap.trace_eq_neg_charpoly_nextCoeff, LinearMap.trace_eq_neg_charpoly_nextCoeff,
    e.charpoly_frobeniusEnd]

end FrobeniusModule

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The image `φ(x) = x ≫ φ` of a rational point under a morphism of `k₀`-schemes. -/
noncomputable def Scheme.Hom.mapFieldPoints (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K : Type u) [Field K] [Algebra k₀ K]
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints K :=
  ⟨x.1 ≫ φ, by rw [Category.assoc, CategoryTheory.comp_over, x.2]⟩

omit [Finite k₀] in
@[simp]
lemma Scheme.Hom.mapFieldPoints_coe (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K : Type u) [Field K] [Algebra k₀ K]
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    (φ.mapFieldPoints K x).1 = x.1 ≫ φ :=
  rfl

omit [Finite k₀] [Y.Over (Spec (CommRingCat.of k₀))] in
/-- The image point of a rational point with values in a finite field has finite residue
field: the residue field embeds into the coefficient field. -/
theorem Scheme.Hom.mem_finitePoints_of_fieldPoints {K : Type u} [Field K] [Algebra k₀ K]
    [Finite K] (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    x.1.base (IsLocalRing.closedPoint K) ∈ X.finitePoints := by
  obtain ⟨ι, -⟩ := Scheme.exists_eq_spec_map_comp_fromSpecResidueField x.1 _ rfl
  exact X.mem_finitePoints.2 (Finite.of_injective _ ι.hom.injective)

omit [Finite k₀] in
/-- The geometric point over the image `φ(x)` of a rational point is the image under the base
change `φ̄` of the geometric point over `x`. -/
theorem Scheme.Hom.geometricFiberPoint_comp_geometricFiberMap (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] {K : Type u} [Field K] [Algebra k₀ K]
    (ι : K →ₐ[k₀] AlgebraicClosure k₀) (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint ι x.1 x.2 ≫
        Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))) =
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint ι (φ.mapFieldPoints K x).1
        (φ.mapFieldPoints K x).2 := by
  ext1 <;> simp

namespace WeilSheaf

omit [Y.Over (Spec (CommRingCat.of k₀))] in
/-- The trace of the Frobenius of the stalk at a geometric point only depends on the point. -/
theorem trace_frobeniusEnd_stalkAt_eq_of_eq (F : WeilSheaf k₀ l X)
    {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (h : s = s') (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hs' : s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s') :
    LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s m hs).frobeniusEnd =
      LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s' m hs').frobeniusEnd := by
  subst h
  rfl

/-- The trace function at a rational point only depends on the image point: at points with the
same image the stalks are taken at geometric points over the same point of `X`
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow`). -/
theorem traceFunction_eq_of_base_eq (F : WeilSheaf k₀ l X) (n : ℕ)
    {x y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)}
    (h : x.1.base (IsLocalRing.closedPoint _) = y.1.base (IsLocalRing.closedPoint _)) :
    F.traceFunction n x = F.traceFunction n y := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have hx := Scheme.Hom.mem_finitePoints_of_fieldPoints x
  rw [F.traceFunction_eq_trace_frobeniusEnd_stalk_pow n x ⟨_, hx⟩ rfl,
    F.traceFunction_eq_trace_frobeniusEnd_stalk_pow n y ⟨_, hx⟩ h.symm]

/-- The stalk of `φ^* F` at a geometric point `t` is the stalk of `F` at `t ≫ φ̄`, compatibly
with the Frobenius (`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_of_upperStar`), so the
traces of the Frobenius agree. -/
theorem trace_frobeniusEnd_stalkAt_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ t)
    (ht' : (t ≫ Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫
        (t ≫ Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))) :
    LinearMap.trace (PadicAlgCl l) _ (((upperStar φ).obj F).stalkAt t m ht).frobeniusEnd =
      LinearMap.trace (PadicAlgCl l) _ (F.stalkAt _ m ht').frobeniusEnd := by
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap φ
      (comp_over φ (Spec (CommRingCat.of k₀))))^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X ⟶ ((WeilSheaf.upperStar φ).obj F).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap φ
      (comp_over φ (Spec (CommRingCat.of k₀))))^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X)))
  obtain ⟨e⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (WeilSheaf.upperStar φ).obj F)
    (θ := 𝟙 _) (upperStar_frobeniusStr_compatible (φ := φ) F) t m ht ht'
  exact e.trace_frobeniusEnd

/-- The trace function of a pullback is the composite with the morphism on rational points:
the stalk of `φ^* F` at the geometric point over `x` is the stalk of `F` at the geometric point
over `φ(x)` (`AlgebraicGeometry.WeilSheaf.trace_frobeniusEnd_stalkAt_upperStar`). -/
theorem traceFunction_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((upperStar φ).obj F).traceFunction n x = F.traceFunction n (φ.mapFieldPoints _ x) := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have ht := Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) n IsAlgClosed.lift x
  have ht' := Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
    (Y ↘ Spec (CommRingCat.of k₀)) n IsAlgClosed.lift (φ.mapFieldPoints _ x)
  have hc := Scheme.Hom.geometricFiberPoint_comp_geometricFiberMap φ IsAlgClosed.lift x
  exact (trace_frobeniusEnd_stalkAt_upperStar φ F _ n ht (hc ▸ ht')).trans
    (F.trace_frobeniusEnd_stalkAt_eq_of_eq hc n _ ht')

end WeilSheaf

namespace WeilComplex

/-- The underlying object of the cohomology sheaf `𝓗ʲ(K)` is the cohomology object of the
underlying object of `K`. -/
noncomputable def homologySheafObjIso (j : ℤ) (K : WeilComplex k₀ l X) :
    ((homologySheaf j).obj K).obj ≅ (_root_.DerivedCategory.homologyFunctor _ j).obj K.obj :=
  Iso.refl _

/-- The underlying object of the pullback `φ^* K` of a Weil complex. -/
noncomputable def upperStarObjIso (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l Y) :
    ((upperStar φ).obj K).obj ≅
      (ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategory.obj K.obj :=
  Iso.refl _

/-- The underlying object of the pullback `φ^* F` of a Weil sheaf. -/
noncomputable def _root_.AlgebraicGeometry.WeilSheaf.upperStarObjIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y) :
    ((WeilSheaf.upperStar φ).obj F).obj ≅ (ProEtaleWeilSheaf.upperStar k₀ l φ).obj F.obj :=
  Iso.refl _

/-- Pullback commutes with the cohomology sheaves: `𝓗ʲ(φ^* K) ≅ φ^* 𝓗ʲ(K)`, the pullback of
pro-étale Weil sheaves being exact. -/
noncomputable def homologySheafUpperStarIso (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (j : ℤ) (K : WeilComplex k₀ l Y) :
    (homologySheaf j).obj ((upperStar φ).obj K) ≅
      (WeilSheaf.upperStar φ).obj ((homologySheaf j).obj K) :=
  ObjectProperty.isoMk _
    (homologySheafObjIso j _ ≪≫ (_root_.DerivedCategory.homologyFunctor _ j).mapIso
      (upperStarObjIso φ K) ≪≫
    ((Functor.mapDerivedCategoryHomologyFunctorIso (ProEtaleWeilSheaf.upperStar k₀ l φ) j).app
      K.obj).symm ≪≫
    (ProEtaleWeilSheaf.upperStar k₀ l φ).mapIso (homologySheafObjIso j K).symm ≪≫
    (WeilSheaf.upperStarObjIso φ _).symm)

/-- A shift `[a]` multiplies the trace function by `(-1)ᵃ`. -/
theorem traceFunction_shift (K : WeilComplex k₀ l X) (a : ℤ) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((shiftFunctor (WeilComplex k₀ l X) a).obj K).traceFunction n x =
      (a.negOnePow : ℤ) • K.traceFunction n x := by
  obtain ⟨S, hS⟩ := K.exists_finset_isZero_homologySheaf
  have hS' (j : ℤ) (hj : j ∉ S.map (Equiv.subRight a).toEmbedding) :
      IsZero ((homologySheaf j).obj ((shiftFunctor (WeilComplex k₀ l X) a).obj K)) :=
    (hS (a + j) fun h ↦ hj (Finset.mem_map.2 ⟨a + j, h, by simp⟩)).of_iso
      (homologySheafShiftIso K a j (a + j) rfl)
  rw [traceFunction_eq_sum _ _ hS', traceFunction_eq_sum _ _ hS, Finset.sum_map,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Equiv.coe_toEmbedding, Equiv.subRight_apply,
    WeilSheaf.traceFunction_congr (homologySheafShiftIso K a (i - a) _ rfl), add_sub_cancel,
    Int.negOnePow_sub, Units.val_mul, mul_comm, mul_smul]

/-- The trace function of a pullback is the composite with the morphism on rational points:
`t_{φ^* K}(x) = t_K(φ(x))`. -/
theorem traceFunction_upperStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l Y) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((upperStar φ).obj K).traceFunction n x = K.traceFunction n (φ.mapFieldPoints _ x) := by
  refine finsum_congr fun j ↦ congrArg _ ?_
  rw [← WeilSheaf.traceFunction_upperStar]
  exact WeilSheaf.traceFunction_congr (homologySheafUpperStarIso φ j K) n x

/-- The trace function is invariant under `k₀`-automorphisms of the coefficient field of the
rational points: `t_K(σ(x)) = t_K(x)`, the local Frobenius operators at the geometric points
over `x` and `σ(x)` being conjugate. -/
theorem traceFunction_fieldPointsCongr (K : WeilComplex k₀ l X) (n : ℕ)
    (σ : FiniteField.galoisExtension k₀ n ≃ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    K.traceFunction n ((X ↘ Spec (CommRingCat.of k₀)).fieldPointsCongr σ x) =
      K.traceFunction n x :=
  finsum_congr fun _ ↦ congrArg _ (WeilSheaf.traceFunction_eq_of_base_eq _ n
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg x.1.base (Subsingleton.elim _ _))))

end WeilComplex

end AlgebraicGeometry
