/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction

/-!
# Nakayama's lemma for constructible `𝒪_E`-module objects

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`, and let `X` be a noetherian scheme. A constructible `𝒪_{E,X}`-module object `M` on
`X_proét` whose reduction `M ⊗_{𝒪_{E,X}} 𝔽_{E,X}` vanishes is zero
(`ProEtale.isZero_of_isConstructibleModuleObject_of_isZero_extendScalars`).

## The argument

1. *Reduction to finitely presented modules.* The strata `Xₐ` of a stratification of `X` are
   quasi-compact, so finitely many affine opens `V` of members of pro-étale covers of the strata
   cover `X`; the composites `g : V ⟶ X` are quasi-compact, `X` being quasi-separated, and the
   pullbacks `g^* M` are finitely presented. Pullbacks along such a finite jointly surjective
   family detect zero objects, and they commute with the reduction
   (`ProEtale.CondensedRing.pullIso`).
2. *Matrices of functions.* For any scheme `V`, the global sections of `𝒪_{E,V}` and `𝔽_{E,V}`
   are the continuous functions `V → 𝒪_E` and `V → 𝔽_E`
   (`ProEtale.continuousMapCoefficientSectionRingHom_bijective`, from Bhatt–Scholze, Lemma
   4.2.12), compatibly with the residue map. So a morphism `A : 𝒪_{E,V}^m ⟶ 𝒪_{E,V}^n` is a
   matrix of continuous functions `V → 𝒪_E`, and the reduction of `A` is the matrix of residues.
3. *Nakayama for matrices.* If the reduction of `A` is an epimorphism, the residue matrix is
   surjective at every point `v`: a row vector killing it at `v` is, multiplied by the indicator
   of the clopen set where the residue matrix is constant, a row vector of functions killing the
   reduction of `A`. Lifting right inverses of the residue matrices locally constantly, `A` gets a
   right inverse of the form `B (A B)⁻¹`, the determinant of `A B` being a unit
   (`ContinuousMap.exists_mul_eq_one_of_forall_residue`). Hence `A` is an epimorphism, and its
   cokernel vanishes (`ProEtale.isZero_of_isFinitelyPresented_of_isZero_extendScalars`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

/-! ### Nakayama's lemma for matrices of continuous functions -/

namespace Matrix

variable {k : Type*} [Field k]

/-- Over a field, a matrix whose rows are linearly independent has a right inverse. -/
lemma exists_mul_eq_one_of_vecMul_eq_zero {n m : ℕ} (M : Matrix (Fin n) (Fin m) k)
    (h : ∀ c : Fin n → k, c ᵥ* M = 0 → c = 0) : ∃ B : Matrix (Fin m) (Fin n) k, M * B = 1 := by
  rw [← mulVec_surjective_iff_exists_right_inverse]
  have hinj : Function.Injective M.vecMul := fun c c' hc ↦ by
    rw [← sub_eq_zero]
    exact h _ (by rw [sub_vecMul]; exact sub_eq_zero.2 hc)
  have hr : LinearMap.range M.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Module.finrank_fintype_fun_eq_card]
    exact (Matrix.vecMul_injective_iff.1 hinj).rank_matrix
  intro y
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 hr y
  exact ⟨x, hx⟩

end Matrix

namespace ContinuousMap

variable {V : Type*} [TopologicalSpace V] {O k : Type*} [CommRing O] [TopologicalSpace O]
  [IsTopologicalRing O] [Field k] [TopologicalSpace k] [DiscreteTopology k]

/-- **Nakayama's lemma for matrices of continuous functions.** Let `π : O → k` be a continuous
surjective ring homomorphism onto a discrete field such that elements with invertible image are
invertible, and such that pointwise invertible continuous functions `V → O` are invertible. Let `t`
be an `n × m` matrix of continuous functions `V → O` such that every row vector `y` of continuous
functions with `π (y t) = 0` satisfies `π y = 0`. Then `t` has a right inverse. -/
theorem exists_mul_eq_one_of_forall_residue (π : O →+* k) (hπ : Continuous π)
    (hsurj : Function.Surjective π) (hunit : ∀ x, IsUnit (π x) → IsUnit x)
    (hinv : ∀ d : C(V, O), (∀ v, IsUnit (d v)) → IsUnit d)
    {n m : ℕ} (t : Matrix (Fin n) (Fin m) C(V, O))
    (H : ∀ y : Fin n → C(V, O), (∀ b v, π ((∑ a, y a * t a b) v) = 0) → ∀ a v, π (y a v) = 0) :
    ∃ s : Matrix (Fin m) (Fin n) C(V, O), t * s = 1 := by
  classical
  let lift := Function.surjInv hsurj
  have hlift (x : k) : π (lift x) = x := Function.surjInv_eq hsurj x
  let T : V → Matrix (Fin n) (Fin m) O := fun v ↦ Matrix.of fun a b ↦ t a b v
  let Tb : V → Matrix (Fin n) (Fin m) k := fun v ↦ (T v).map π
  have hT : Continuous T := continuous_matrix fun a b ↦ (t a b).continuous
  -- the sets where the residue matrix is constant are clopen
  have hZ (v : V) : IsClopen {w | Tb w = Tb v} := by
    have : {w | Tb w = Tb v} = ⋂ a, ⋂ b, (fun w ↦ π (t a b w)) ⁻¹' {Tb v a b} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h a b ↦ congrFun (congrFun h a) b, fun h ↦ Matrix.ext h⟩
    rw [this]
    exact isClopen_iInter_of_finite fun a ↦ isClopen_iInter_of_finite fun b ↦
      (isClopen_discrete _).preimage (hπ.comp (t a b).continuous)
  have hloc : IsLocallyConstant Tb :=
    IsLocallyConstant.iff_exists_open _ |>.2 fun v ↦ ⟨_, (hZ v).isOpen, rfl, fun _ h ↦ h⟩
  -- pointwise, the residue matrix has a right inverse
  have hB (v : V) : ∃ B : Matrix (Fin m) (Fin n) k, Tb v * B = 1 := by
    refine Matrix.exists_mul_eq_one_of_vecMul_eq_zero _ fun c hc ↦ ?_
    let y : Fin n → C(V, O) := fun a ↦
      ContinuousMap.const V (lift (c a)) * (LocallyConstant.charFn O (hZ v)).toContinuousMap
    have hy (a : Fin n) (w : V) : y a w = lift (c a) * Set.indicator {w | Tb w = Tb v} 1 w := rfl
    have := H y fun b w ↦ by
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.mul_apply, hy, map_sum,
        map_mul, hlift]
      by_cases hw : w ∈ {w | Tb w = Tb v}
      · simp only [Set.indicator_of_mem hw, Pi.one_apply, map_one]
        have hw' : ∀ a, π (t a b w) = Tb v a b := fun a ↦ congrFun (congrFun hw a) b
        simp only [hw']
        simpa [Matrix.vecMul, dotProduct] using congrFun hc b
      · simp [Set.indicator_of_notMem hw]
    funext a
    simpa [hy, hlift] using this a v
  -- a locally constant choice of lifts of right inverses
  let χ : Matrix (Fin n) (Fin m) k → Matrix (Fin m) (Fin n) O := fun M ↦
    if h : ∃ B : Matrix (Fin m) (Fin n) k, M * B = 1 then h.choose.map lift else 0
  have hχ (v : V) : Tb v * (χ (Tb v)).map π = 1 := by
    have h := hB v
    simp only [χ, dite_eq_left h, Matrix.map_map]
    convert h.choose_spec
    ext i j
    exact hlift _
  have hχc : Continuous fun v ↦ χ (Tb v) := (hloc.comp χ).continuous
  let D : V → Matrix (Fin n) (Fin n) O := fun v ↦ T v * χ (Tb v)
  have hDc : Continuous D := hT.matrix_mul hχc
  have hD (v : V) : IsUnit (D v).det := by
    refine hunit _ ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
    change IsUnit (Tb v * (χ (Tb v)).map π).det
    rw [hχ v, Matrix.det_one]
    exact isUnit_one
  let d : C(V, O) := ⟨fun v ↦ (D v).det, hDc.matrix_det⟩
  obtain ⟨w, hw⟩ := (hinv d hD).exists_left_inv
  have hw' (v : V) : w v * (D v).det = 1 :=
    congrArg (fun f : C(V, O) ↦ f v) hw
  let S : V → Matrix (Fin m) (Fin n) O := fun v ↦ χ (Tb v) * (w v • (D v).adjugate)
  have hSc : Continuous S := hχc.matrix_mul (w.continuous.smul hDc.matrix_adjugate)
  have hTS (v : V) : T v * S v = 1 := by
    simp only [S, ← Matrix.mul_assoc, Matrix.mul_smul]
    change w v • (D v * (D v).adjugate) = 1
    rw [Matrix.mul_adjugate, smul_smul, hw', one_smul]
  refine ⟨Matrix.of fun b c ↦ ⟨fun v ↦ S v b c, hSc.matrix_elem b c⟩, ?_⟩
  ext a c v
  have h := congrFun (congrFun (hTS v) a) c
  simp only [Matrix.mul_apply, T, Matrix.of_apply] at h
  simp only [Matrix.mul_apply, Matrix.of_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.mul_apply, ContinuousMap.coe_mk, h, Matrix.one_apply]
  split_ifs <;> rfl

end ContinuousMap

/-! ### Nakayama's lemma for finitely presented module objects -/

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [BraidedCategory C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [IsCommMonObj R] [PreservesFiniteColimits (tensorLeft R)]
  [MonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- **Nakayama's lemma for finitely presented module objects over rings of functions.** Let
`φ : R ⟶ S` be a morphism of algebra objects with `R` commutative. Assume that the endomorphisms
of the regular module `R` are the continuous functions `V → O` (via `eR`), that the continuous
functions `V → k` act faithfully on the regular module `S` (via `eS`), where `π : O → k` is as in
`ContinuousMap.exists_mul_eq_one_of_forall_residue`, and that extension of scalars along `φ`
corresponds to postcomposition with `π`. Then a finitely presented `R`-module whose extension of
scalars to `S` vanishes is zero: a presentation matrix becomes surjective after reduction, hence
has a right inverse. -/
theorem isZero_of_isFinitelyPresented_of_isZero_extendScalars_of_continuousMap
    {V O k : Type*} [TopologicalSpace V] [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Field k] [TopologicalSpace k] [DiscreteTopology k]
    (π : O →+* k) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hunit : ∀ x, IsUnit (π x) → IsUnit x)
    (hinv : ∀ d : C(V, O), (∀ v, IsUnit (d v)) → IsUnit d)
    (eR : C(V, O) →+* End (regular R)) (heR : Function.Bijective eR)
    (eS : C(V, k) →+* End (regular S)) (heS : Function.Injective eS)
    (hcompat : ∀ f, (extendScalarsObjRegularIso φ).inv ≫ (extendScalars φ).map (eR f).asHom =
      (eS ((⟨π, hπ⟩ : C(O, k)).comp f)).asHom ≫ (extendScalarsObjRegularIso φ).inv)
    (N : Mod C R) (hN : IsFinitelyPresented R N) (h : IsZero ((extendScalars φ).obj N)) :
    IsZero N := by
  have : (extendScalars φ).Additive := (extendRestrictAdjunction φ).left_adjoint_additive
  have : PreservesColimits (extendScalars φ) :=
    (extendRestrictAdjunction φ).leftAdjoint_preservesColimits
  obtain ⟨n, m, A, ⟨i⟩⟩ := hN
  have hext0 (f : C(V, O)) (hf : (extendScalars φ).map (eR f).asHom = 0) (v : V) :
      π (f v) = 0 := by
    have h1 : (eS ((⟨π, hπ⟩ : C(O, k)).comp f)).asHom ≫
        (extendScalarsObjRegularIso φ).inv = 0 := by
      rw [← hcompat, hf, comp_zero]
    have h2 : eS ((⟨π, hπ⟩ : C(O, k)).comp f) = 0 :=
      End.ext ((cancel_mono _).1 (h1.trans zero_comp.symm))
    have h3 : (⟨π, hπ⟩ : C(O, k)).comp f = 0 := heS (h2.trans (map_zero eS).symm)
    exact congrArg (fun g ↦ g v) h3
  have hepi : Epi ((extendScalars φ).map A) := Preadditive.epi_of_isZero_cokernel _
    ((h.of_iso ((extendScalars φ).mapIso i).symm).of_iso (PreservesCokernel.iso _ A).symm)
  let eR' := RingEquiv.ofBijective eR heR
  let t : Matrix (Fin n) (Fin m) C(V, O) := Matrix.of fun a b ↦
    eR'.symm (.of (biproduct.ι (fun _ ↦ regular R) b ≫ A ≫ biproduct.π (fun _ ↦ regular R) a))
  have ht (a : Fin n) (b : Fin m) : (eR (t a b)).asHom =
      biproduct.ι (fun _ ↦ regular R) b ≫ A ≫ biproduct.π (fun _ ↦ regular R) a :=
    congrArg End.asHom (eR'.apply_symm_apply _)
  -- composites through a finite free module are sums over the summands
  have hsum {p : ℕ} {Y Z : Mod C R} (f : Y ⟶ finiteFree R p) (g : finiteFree R p ⟶ Z) :
      f ≫ g = ∑ a, (f ≫ biproduct.π (fun _ ↦ regular R) a) ≫
        (biproduct.ι (fun _ ↦ regular R) a ≫ g) := by
    conv_lhs => rw [← Category.id_comp g, ← biproduct.total]
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    simp only [Category.assoc]
  have H : ∀ y : Fin n → C(V, O), (∀ b v, π ((∑ a, y a * t a b) v) = 0) →
      ∀ a v, π (y a v) = 0 := by
    intro y hy
    let yt : finiteFree R n ⟶ regular R := biproduct.desc fun a ↦ (eR (y a)).asHom
    have hrow (b : Fin m) :
        (extendScalars φ).map (biproduct.ι (fun _ ↦ regular R) b ≫ A ≫ yt) = 0 := by
      have e : biproduct.ι (fun _ ↦ regular R) b ≫ A ≫ yt = (eR (∑ a, y a * t a b)).asHom := by
        rw [← Category.assoc, hsum _ yt, map_sum, End.sum_asHom]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [map_mul, End.mul_asHom, biproduct.ι_desc, ht]
        simp only [Category.assoc]
      rw [e]
      refine (cancel_epi (extendScalarsObjRegularIso φ).inv).1 ?_
      rw [hcompat, comp_zero]
      have : (⟨π, hπ⟩ : C(O, k)).comp (∑ a, y a * t a b) = 0 :=
        ContinuousMap.ext fun v ↦ hy b v
      rw [this, map_zero, End.zero_asHom, zero_comp]
    have h1 : (extendScalars φ).map (A ≫ yt) = 0 := by
      rw [← Category.id_comp (A ≫ yt), ← biproduct.total, Preadditive.sum_comp, Functor.map_sum]
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      rw [Category.assoc, Functor.map_comp, hrow b, comp_zero]
    have h2 : (extendScalars φ).map yt = 0 := by
      rw [Functor.map_comp] at h1
      exact (cancel_epi _).1 (h1.trans comp_zero.symm)
    intro a v
    refine hext0 _ ?_ v
    rw [← biproduct.ι_desc (fun a ↦ (eR (y a)).asHom) a, Functor.map_comp]
    exact (congrArg _ h2).trans comp_zero
  obtain ⟨s, hs⟩ := ContinuousMap.exists_mul_eq_one_of_forall_residue π hπ hsurj hunit hinv t H
  -- `A` has a right inverse
  let D : finiteFree R n ⟶ finiteFree R m := biproduct.matrix fun c b ↦ (eR (s b c)).asHom
  have hDA : D ≫ A = 𝟙 _ := by
    refine biproduct.hom_ext' _ _ fun c ↦ biproduct.hom_ext _ _ fun a ↦ ?_
    have e1 : (biproduct.ι (fun _ ↦ regular R) c ≫ D ≫ A) ≫ biproduct.π (fun _ ↦ regular R) a =
        (eR ((t * s) a c)).asHom := by
      have e : (biproduct.ι (fun _ ↦ regular R) c ≫ D ≫ A) ≫ biproduct.π (fun _ ↦ regular R) a =
          (biproduct.ι (fun _ ↦ regular R) c ≫ D) ≫ (A ≫ biproduct.π (fun _ ↦ regular R) a) := by
        simp only [Category.assoc]
      rw [e, hsum (biproduct.ι _ c ≫ D) (A ≫ biproduct.π _ a), Matrix.mul_apply, map_sum,
        End.sum_asHom]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [biproduct.ι_matrix, biproduct.lift_π, map_mul, End.mul_asHom, ht]
    rw [e1, hs, Category.comp_id, biproduct.ι_π, Matrix.one_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  have : Epi A := (IsSplitEpi.mk' ⟨D, hDA⟩).epi
  exact (isZero_cokernel_of_epi A).of_iso i

end CategoryTheory.Mod

/-! ### The ring of integers and its residue field -/

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- An integer whose residue is invertible is invertible. -/
lemma isUnit_of_isUnit_integersResidue (x : integers ℓ E)
    (h : IsUnit (integersResidue ℓ E x)) : IsUnit x :=
  (IsLocalRing.residue_ne_zero_iff_isUnit x).1 h.ne_zero

/-- A continuous function to `𝒪_E` with invertible values is invertible: its pointwise inverse is
continuous. -/
lemma isUnit_continuousMap_integers {V : Type*} [TopologicalSpace V] :
    letI := normedFieldOfAlgebra ℓ E
    ∀ d : C(V, integers ℓ E), (∀ v, IsUnit (d v)) → IsUnit d := by
  let := normedFieldOfAlgebra ℓ E
  intro d hd
  have hne (v : V) : ((d v : integers ℓ E) : E) ≠ 0 := fun h ↦
    (hd v).ne_zero (Subtype.ext h)
  have hmem (v : V) : ((d v : integers ℓ E) : E)⁻¹ ∈ integers ℓ E := by
    have h : (((hd v).unit⁻¹ : (integers ℓ E)ˣ) : integers ℓ E) * d v = 1 := by
      simp
    have h' : ((((hd v).unit⁻¹ : (integers ℓ E)ˣ) : integers ℓ E) : E) * (d v : E) = 1 := by
      exact_mod_cast congrArg (fun x : integers ℓ E ↦ (x : E)) h
    rw [← eq_inv_of_mul_eq_one_left h']
    exact SetLike.coe_mem _
  let g : C(V, integers ℓ E) := ⟨fun v ↦ ⟨((d v : integers ℓ E) : E)⁻¹, hmem v⟩,
    ((continuous_subtype_val.comp d.continuous).inv₀ hne).subtype_mk _⟩
  refine IsUnit.of_mul_eq_one g (ContinuousMap.ext fun v ↦ Subtype.ext ?_)
  exact mul_inv_cancel₀ (hne v)

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

/-! ### Nakayama's lemma for finitely presented `𝒪_{E,V}`-modules -/

section FinitelyPresented

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The residue map `𝒪_{E,V} ⟶ 𝔽_{E,V}` on global sections is the postcomposition of continuous
functions `V → 𝒪_E` with the residue map `𝒪_E → 𝔽_E`. -/
lemma Γ_map_padicIntegersToResidueField (V : Scheme.{u}) :
    letI := normedFieldOfAlgebra ℓ E
    haveI := isUltrametricDist_ofAlgebra ℓ E
    ∀ f : C(V, integers ℓ E),
      Γ.map (padicIntegersToResidueField V ℓ E)
          (continuousMapCoefficientSectionRingHom V (integers ℓ E) f) =
        continuousMapCoefficientSectionRingHom V (integersResidueField ℓ E)
          ((⟨integersResidue ℓ E, continuous_integersResidue ℓ E⟩ :
            C(integers ℓ E, integersResidueField ℓ E)).comp f) := by
  let := normedFieldOfAlgebra ℓ E
  have := isUltrametricDist_ofAlgebra ℓ E
  intro f
  have hn := continuousMapComparison_naturality V (integersResidue ℓ E)
    (continuous_integersResidue ℓ E)
  have hn' : inv (continuousMapComparison V (integers ℓ E)) ≫
      padicIntegersToResidueField V ℓ E =
      (sheafCompose (ProEt.topology V) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (continuousMapRingSheafMap V (integersResidue ℓ E) (continuous_integersResidue ℓ E)) ≫
        inv (continuousMapComparison V (integersResidueField ℓ E)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
    rfl
  refine Γ.ext ?_
  rw [Γ.map_hom, continuousMapCoefficientSectionRingHom_hom,
    continuousMapCoefficientSectionRingHom_hom, Category.assoc, hn', ← Category.assoc]
  congr 1
  refine Sheaf.unitHomEval_injective (J := ProEt.topology V) (ProEt.isTerminalMkId V) _ ?_
  refine (Sheaf.unitHomEval_comp (J := ProEt.topology V) _ _ _).trans ?_
  rw [unitHomEval_continuousMapSectionRingHom, unitHomEval_continuousMapSectionRingHom]
  rfl


omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **Nakayama's lemma for finitely presented `𝒪_{E,V}`-modules.** On any scheme `V`, a finitely
presented `𝒪_{E,V}`-module object whose reduction `N ⊗_{𝒪_{E,V}} 𝔽_{E,V}` vanishes is zero. -/
theorem isZero_of_isFinitelyPresented_of_isZero_extendScalars {V : Scheme.{u}}
    (N : Mod (Sheaf (ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V))
    (hN : Mod.IsFinitelyPresented _ N)
    (h : IsZero ((Mod.extendScalars (padicIntegersToResidueField V ℓ E)).obj N)) :
    IsZero N := by
  let := normedFieldOfAlgebra ℓ E
  have := isUltrametricDist_ofAlgebra ℓ E
  refine Mod.isZero_of_isFinitelyPresented_of_isZero_extendScalars_of_continuousMap
    (padicIntegersToResidueField V ℓ E) (integersResidue ℓ E)
    (continuous_integersResidue ℓ E) (integersResidue_surjective ℓ E)
    (isUnit_of_isUnit_integersResidue ℓ E) (isUnit_continuousMap_integers ℓ E)
    (Mod.regularEndRingHom.comp (continuousMapCoefficientSectionRingHom V _))
    (Mod.regularEndRingHom_bijective.comp (continuousMapCoefficientSectionRingHom_bijective V _))
    (Mod.regularEndRingHom.comp (continuousMapCoefficientSectionRingHom V _))
    (Mod.regularEndRingHom_bijective.comp
      (continuousMapCoefficientSectionRingHom_bijective V _)).1 (fun f ↦ ?_) N hN h
  have := Mod.extendScalarsObjRegularIso_inv_comp_map (padicIntegersToResidueField V ℓ E)
    (continuousMapCoefficientSectionRingHom V _ f)
  rw [Γ_map_padicIntegersToResidueField] at this
  exact this

end FinitelyPresented
/-! ### Constructible module objects -/

section Constructible

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- Let `g : V ⟶ X` be a morphism along which the pullback of an `𝒪_{E,X}`-module `M` is finitely
presented. If the reduction of `M` vanishes, so does `g^* M`: the reduction commutes with
pullbacks. -/
lemma isZero_upperStar_of_isZero_extendScalars {X V : Scheme.{u}} (g : V ⟶ X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    (hM : Mod.IsFinitelyPresented _ ((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M))
    (h : IsZero ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).obj M)) :
    IsZero ((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M) :=
  isZero_of_isFinitelyPresented_of_isZero_extendScalars ℓ E _ hM
    ((((g)^*⟦Profinite.continuousMapRingObj (integersResidueField ℓ E)⟧).map_isZero h).of_iso
      ((pullIso (Profinite.padicIntegersRingObjToResidueField ℓ E) g).app M))

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- **Nakayama's lemma for constructible `𝒪_E`-module objects.** On a noetherian scheme `X`, a
constructible `𝒪_{E,X}`-module object `M` whose reduction `M ⊗_{𝒪_{E,X}} 𝔽_{E,X}` vanishes is
zero. -/
theorem isZero_of_isConstructibleModuleObject_of_isZero_extendScalars
    {X : Scheme.{u}} [IsNoetherian X]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))
    (hM : IsConstructibleModuleObject _ M)
    (h : IsZero ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).obj M)) :
    IsZero M := by
  obtain ⟨S, hS⟩ := hM
  choose 𝒰 h𝒰 using hS
  -- the strata are quasi-compact
  have hc (a : Fin S.n) : CompactSpace (S.domain a) := by
    have := (S.immersion a).isEmbedding.isInducing.noetherianSpace
    infer_instance
  -- finitely many affine opens of members of the covers cover each stratum
  have hqc (a : Fin S.n) : QuasiCompactCover (𝒰 a).toPreZeroHypercover := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact (show _ ∈ propQCPrecoverage @WeaklyEtale _ from (𝒰 a).mem₀).1
  have hfin (a : Fin S.n) := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    (𝒰 a).toPreZeroHypercover (U := ⊤) (by simpa using isCompact_univ)
  choose N j W hW hcov using hfin
  have hW' (a : Fin S.n) (i : Fin (N a)) : IsAffine (W a i) := hW a i
  have hg : ∀ x, ∃ p : Σ a : Fin S.n, Fin (N a),
      x ∈ Set.range ((W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1) := by
    intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    rw [← S.range_immersion a] at ha
    obtain ⟨y, rfl⟩ := ha
    have hy : y ∈ ⋃ i, (𝒰 a).f (j a i) '' (W a i) := by
      rw [hcov a]
      trivial
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨w, rfl⟩ : z ∈ Set.range (W a i).ι := by
      rw [Scheme.Opens.range_ι]
      exact hz
    exact ⟨⟨a, i⟩, w, rfl⟩
  have hz (a : Fin S.n) (i : Fin (N a)) : IsZero ((((W a i).ι ≫ (𝒰 a).f (j a i) ≫
      S.immersion a))^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M) := by
    refine isZero_upperStar_of_isZero_extendScalars ℓ E _ M ?_ h
    have h₁ := isFinitelyPresented_upperStar_of_comap_iso (Profinite.padicIntegersRingObj ℓ E)
      ((𝒰 a).f (j a i)) (condensedPullbackHom _ (S.immersion a))
      (comapUpperStarObjIso _ (S.immersion a) M) (h𝒰 a (j a i))
    exact (CondensedRing.IsFinitelyPresented.upperStar _ (W a i).ι h₁).of_iso
      (((W a i).ι)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.mapIso
        ((CondensedRing.upperStarComp _ ((𝒰 a).f (j a i)) (S.immersion a)).app M).symm ≪≫
        ((CondensedRing.upperStarComp _ (W a i).ι ((𝒰 a).f (j a i) ≫ S.immersion a)).app M).symm)
  have hqcg (p : Σ a : Fin S.n, Fin (N a)) :
      QuasiCompact ((W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1) :=
    have := hW' p.1 p.2
    quasiCompact_of_compactSpace _
  refine CondensedRing.isZero_of_isZero_X (Profinite.padicIntegersRingObj ℓ E)
    ((IsZero.iff_id_eq_zero _).2 ?_)
  refine ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
    (Z := fun p : Σ a : Fin S.n, Fin (N a) ↦ (W p.1 p.2).toScheme)
    (fun p ↦ (W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1) hg (𝟙 M.X) fun p ↦ ?_
  have h₁ := (Mod.forget _).map_isZero (hz p.1 p.2)
  have h₂ := h₁.of_iso (CondensedRing.upperStarObjXIso _ _ M).symm
  exact h₂.eq_of_src _ _

end Constructible

end AlgebraicGeometry.ProEtale
