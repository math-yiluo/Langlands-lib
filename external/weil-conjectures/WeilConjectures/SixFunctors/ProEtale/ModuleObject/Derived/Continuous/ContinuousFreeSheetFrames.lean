/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleLatticeSheetMaps
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFreeSheetGlobalCoordinates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousSheetCoordinateRestriction
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Coordinates of already free sheet modules

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2.
(blueprint: lem-sfb-continuous-free-sheet-frames)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor Matrix

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem natural_linear_map_matrix
    (Y : Scheme.{u}) (E : Type) [NormedField E] (m n : ℕ)
    (F : ∀ B : Y.ProEt,
      C(B.left, Fin m → E) →ₗ[C(B.left, E)] C(B.left, Fin n → E))
    (hF : ∀ (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin m → E)),
      F D (x.comp a.left.base.hom) = (F B x).comp a.left.base.hom) :
    ∃ H : Matrix (Fin n) (Fin m) C(Y, E),
      ∀ (B : Y.ProEt) (x : C(B.left, Fin m → E)) (z : B.left),
        F B x z = (fun i k ↦ H i k (B.hom z)) *ᵥ x z := by
  classical
  let T : Y.ProEt := Scheme.ProEt.mk (𝟙 Y)
  let v (B : Y.ProEt) (k : Fin m) : C(B.left, Fin m → E) :=
    ContinuousMap.const _ (Pi.single k 1)
  let H : Matrix (Fin n) (Fin m) C(Y, E) :=
    fun i k ↦ (ContinuousMap.eval i).comp (F T (v T k))
  refine ⟨H, ?_⟩
  intro B x z
  let a : B ⟶ T := MorphismProperty.Over.homMk B.hom (Category.comp_id _)
  have hv (k : Fin m) : F B (v B k) = (F T (v T k)).comp B.hom.base.hom :=
    hF T B a (v T k)
  let q (k : Fin m) : C(B.left, E) := (ContinuousMap.eval k).comp x
  have hx : x = ∑ k : Fin m, q k • v B k := by
    ext z i
    simp [q, v, Pi.single_apply]
  have hfx : F B x = ∑ k : Fin m, q k • F B (v B k) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [map_smul]
  rw [hfx]
  ext i
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply', Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun f : C(B.left, Fin n → E) ↦ f z i) (hv k)
  change F B (v B k) z i = H i k (B.hom z) at h
  rw [h]
  exact mul_comm _ _

private def eval_matrix {Y : Type u} [TopologicalSpace Y]
    {E : Type} [TopologicalSpace E] {m n : ℕ}
    (H : Matrix (Fin n) (Fin m) C(Y, E)) (y : Y) : Matrix (Fin n) (Fin m) E :=
  fun i k ↦ H i k y

private theorem natural_linear_equiv_matrices
    (Y : Scheme.{u}) (E : Type) [NormedField E] (m n : ℕ)
    (F : ∀ B : Y.ProEt,
      C(B.left, Fin m → E) ≃ₗ[C(B.left, E)] C(B.left, Fin n → E))
    (hF : ∀ (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin m → E)),
      F D (x.comp a.left.base.hom) = (F B x).comp a.left.base.hom) :
    ∃ (H : Matrix (Fin n) (Fin m) C(Y, E))
      (K : Matrix (Fin m) (Fin n) C(Y, E)),
      (∀ y : Y, (eval_matrix H y * eval_matrix K y) = 1) ∧
      (∀ y : Y, (eval_matrix K y * eval_matrix H y) = 1) ∧
      ∀ (B : Y.ProEt) (x : C(B.left, Fin m → E)) (z : B.left),
        F B x z = (fun i k ↦ H i k (B.hom z)) *ᵥ x z := by
  classical
  obtain ⟨H, hH⟩ := natural_linear_map_matrix Y E m n
    (fun B ↦ (F B).toLinearMap) hF
  have hFi (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin n → E)) :
      (F D).symm (x.comp a.left.base.hom) =
        ((F B).symm x).comp a.left.base.hom := by
    apply (F D).injective
    rw [LinearEquiv.apply_symm_apply, hF, LinearEquiv.apply_symm_apply]
  obtain ⟨K, hK⟩ := natural_linear_map_matrix Y E n m
    (fun B ↦ (F B).symm.toLinearMap) hFi
  let T : Y.ProEt := Scheme.ProEt.mk (𝟙 Y)
  let v (k : Fin n) : C(Y, Fin n → E) := ContinuousMap.const _ (Pi.single k 1)
  let v' (k : Fin m) : C(Y, Fin m → E) := ContinuousMap.const _ (Pi.single k 1)
  let Hy (y : Y) : Matrix (Fin n) (Fin m) E := fun i k ↦ H i k y
  let Ky (y : Y) : Matrix (Fin m) (Fin n) E := fun i k ↦ K i k y
  have hHK (y : Y) : Hy y * Ky y = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro k
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    calc
      Hy y *ᵥ (Ky y *ᵥ Pi.single k 1) = Hy y *ᵥ ((F T).symm (v k)) y :=
        congrArg (fun x ↦ Hy y *ᵥ x) (hK T (v k) y).symm
      _ = (F T ((F T).symm (v k))) y := (hH T _ y).symm
      _ = Pi.single k 1 := congrArg (fun x : C(Y, Fin n → E) ↦ x y)
        ((F T).apply_symm_apply (v k))
  have hKH (y : Y) : Ky y * Hy y = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro k
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    calc
      Ky y *ᵥ (Hy y *ᵥ Pi.single k 1) = Ky y *ᵥ (F T (v' k)) y :=
        congrArg (fun x ↦ Ky y *ᵥ x) (hH T (v' k) y).symm
      _ = ((F T).symm (F T (v' k))) y := (hK T _ y).symm
      _ = Pi.single k 1 := congrArg (fun x : C(Y, Fin m → E) ↦ x y)
        ((F T).symm_apply_apply (v' k))
  exact ⟨H, K, hHK, hKH, hH⟩

private theorem natural_linear_equiv_rank
    (Y : Scheme.{u}) (E : Type) [NormedField E] (m n : ℕ)
    (F : ∀ B : Y.ProEt,
      C(B.left, Fin m → E) ≃ₗ[C(B.left, E)] C(B.left, Fin n → E))
    (hF : ∀ (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin m → E)),
      F D (x.comp a.left.base.hom) = (F B x).comp a.left.base.hom)
    (y : Y) : m = n := by
  obtain ⟨H, K, hHK, hKH, _⟩ := natural_linear_equiv_matrices Y E m n F hF
  let Hy : Matrix (Fin n) (Fin m) E := fun i k ↦ H i k y
  let Ky : Matrix (Fin m) (Fin n) E := fun i k ↦ K i k y
  let e : (Fin m → E) ≃ₗ[E] (Fin n → E) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin Hy) (Matrix.mulVecLin Ky)
      (by
        apply LinearMap.ext
        intro x
        change Hy *ᵥ (Ky *ᵥ x) = x
        rw [Matrix.mulVec_mulVec]
        change (eval_matrix H y * eval_matrix K y) *ᵥ x = x
        rw [hHK y, Matrix.one_mulVec])
      (by
        apply LinearMap.ext
        intro x
        change Ky *ᵥ (Hy *ᵥ x) = x
        rw [Matrix.mulVec_mulVec]
        change (eval_matrix K y * eval_matrix H y) *ᵥ x = x
        rw [hKH y, Matrix.one_mulVec])
  simpa only [Module.finrank_fin_fun] using e.finrank_eq

private theorem natural_linear_equiv_matrix
    (Y : Scheme.{u}) (E : Type) [NormedField E] (r : ℕ)
    (F : ∀ B : Y.ProEt,
      C(B.left, Fin r → E) ≃ₗ[C(B.left, E)] C(B.left, Fin r → E))
    (hF : ∀ (B D : Y.ProEt) (a : D ⟶ B) (x : C(B.left, Fin r → E)),
      F D (x.comp a.left.base.hom) = (F B x).comp a.left.base.hom) :
    ∃ G : Y → Matrix.GeneralLinearGroup (Fin r) E,
      (∀ i k, Continuous (fun y ↦ (G y).val i k)) ∧
      (∀ i k, Continuous (fun y ↦ ((G y)⁻¹).val i k)) ∧
      ∀ (B : Y.ProEt) (x : C(B.left, Fin r → E)) (z : B.left),
        F B x z = (G (B.hom z)).val *ᵥ x z := by
  obtain ⟨H, K, hHK, hKH, hH⟩ := natural_linear_equiv_matrices Y E r r F hF
  let G (y : Y) : Matrix.GeneralLinearGroup (Fin r) E :=
    ⟨fun i k ↦ H i k y, fun i k ↦ K i k y, hHK y, hKH y⟩
  exact ⟨G, fun i k ↦ (H i k).continuous, fun i k ↦ (K i k).continuous, hH⟩

private def empty_presentation_rank
    (Y : Scheme.{u}) [IsEmpty Y] (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A] (n r : ℕ)
    (Q : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y))
    (p : ContinuousFunctionPresentation Y A (Fin n → A) Q) :
    ContinuousFunctionPresentation Y A (Fin r → A) Q := by
  let e (B : Y.ProEt) : C(B.left, Fin n → A) ≃+ C(B.left, Fin r → A) := by
    have : IsEmpty B.left := ⟨fun z ↦ isEmptyElim (show Y from B.hom z)⟩
    exact
      { toFun := fun _ ↦ 0
        invFun := fun _ ↦ 0
        left_inv := fun _ ↦ Subsingleton.elim _ _
        right_inv := fun _ ↦ Subsingleton.elim _ _
        map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
  refine { sections := fun B ↦ (p.sections B).trans (e B), restrict := ?_, smul := ?_ }
  · intro B D a x
    ext z
    exact isEmptyElim (show Y from D.hom z)
  · intro B a x
    ext z
    exact isEmptyElim (show Y from B.hom z)

/-- Globally free rational and integral modules give coordinates for the actual sheet maps.
There is no covering or splitting assertion here, and no assertion about ranges.

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2;
Bhatt--Scholze, Section 6.8, continuous coefficients and changes of free bases.
(blueprint: lem-sfb-continuous-free-sheet-frames)

Proof. Choose a finite free rational frame on Y and a finite free integral frame
for each pulled-back module t_j*M. Scalar extension carries a finite biproduct
of integral regular modules to the same biproduct of rational regular modules.
The given e, the scalar pullback comparison, and upperStarComp identify these
rationalized frames with g*P. The encoded rational frames are finite products
of the continuous coefficient sheaf. Evaluate the resulting isomorphism at the
terminal pro-etale object Y, and then at a point of Y: invariant basis number
over E identifies each integral frame rank with the rational rank r. The entries
of the isomorphism and its inverse are the coordinates of the constant basis
vectors on Y, hence are continuous functions on Y. Their composite identities
give pointwise inverse matrices G_j. If Y is empty, every section on every test
object is zero, so choose the rational rank and use the unique presentations
and identity matrices; this also covers rank zero.

For an open W, restrict these same frames. The continuous coefficient encoding
commutes with this restriction, so it gives the presentations c and b_j. Apply
naturality to each frame vector and expand any integral section in this finite
basis. The scalar extension unit sends its integral coordinates to the same
coordinates in E. Naturality of comapUpperStarIso, the coefficient pullback
comparison and upperStarComp identifies the normalized composite with precisely
finiteEtaleLatticeSheetEmbedding. This yields the displayed forward equation
for every test object B and section x. This argument does not require p to be
finite, etale or surjective, or the t_j to split a pullback. -/
theorem continuousFreeSheet_frames
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (g : Y ⟶ X) (d : ℕ) (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hP : Mod.IsFree (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((upperStar (Profinite.continuousMapRingObj E) g).obj P))
    (hM : ∀ j, Mod.IsFree (condensedRingObj (integralCoeff l E) Y)
      ((upperStar (integralCoeff l E) (t j)).obj M)) :
    ∃ (r : ℕ) (G : Fin d → Y → Matrix.GeneralLinearGroup (Fin r) E),
      (∀ j i k, Continuous (fun y ↦ (G j y).val i k)) ∧
      (∀ j i k, Continuous (fun y ↦ ((G j y)⁻¹).val i k)) ∧
      ∀ W : Y.Opens, ∃ w' : ∀ j, (W.ι ≫ t j) ≫ p = W.ι ≫ g,
        ∃ c : ContinuousFunctionPresentation W.toScheme (continuousIntegers l E)
            (Fin r → E) ((Mod.comap
              (coefficientMap (integralScalarMap l E) W.toScheme)).obj
              ((upperStar (Profinite.continuousMapRingObj E) (W.ι ≫ g)).obj P)),
        ∃ b : ∀ j, ContinuousFunctionPresentation W.toScheme (continuousIntegers l E)
            (Fin r → continuousIntegers l E)
            ((upperStar (integralCoeff l E) (W.ι ≫ t j)).obj M),
        ∀ (j : Fin d) (B : W.toScheme.ProEt)
          (x : ((continuousRingModuleEquivalence W.toScheme
            (continuousIntegers l E)).functor.obj
            ((upperStar (integralCoeff l E) (W.ι ≫ t j)).obj M)).val.obj (op B))
          (z : B.left),
          c.sections B
            (((continuousRingModuleEquivalence W.toScheme
              (continuousIntegers l E)).functor.map
              (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
                (W.ι ≫ g) (W.ι ≫ t j) (w' j))).val.app (op B) x) z =
            (G j (W.ι (B.hom z))).val *ᵥ
              (fun i ↦ ((b j).sections B x z i : E)) := by
  classical
  obtain ⟨r, n, c, b, F, hF, heq⟩ :=
    continuousFreeSheet_globalCoordinates l E P p M e g d t w hP hM
  by_cases hY : Nonempty Y
  · obtain ⟨y⟩ := hY
    have hn (j : Fin d) : n j = r :=
      natural_linear_equiv_rank Y E (n j) r (F j) (hF j) y
    have hcoord (j : Fin d) :
        ∃ (bj : ContinuousFunctionPresentation Y (continuousIntegers l E)
          (Fin r → continuousIntegers l E) ((upperStar (integralCoeff l E) (t j)).obj M))
          (G : Y → Matrix.GeneralLinearGroup (Fin r) E),
          (∀ i k, Continuous (fun y ↦ (G y).val i k)) ∧
          (∀ i k, Continuous (fun y ↦ ((G y)⁻¹).val i k)) ∧
          ∀ (B : Y.ProEt)
            (x : ((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.obj
              ((upperStar (integralCoeff l E) (t j)).obj M)).val.obj (op B)) (z : B.left),
            c.sections B
              (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
                (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
                  g (t j) (w j))).val.app (op B) x) z =
              (G (B.hom z)).val *ᵥ (fun i ↦ (bj.sections B x z i : E)) := by
      rcases hn j with rfl
      obtain ⟨G, hG, hGi, hmatrix⟩ :=
        natural_linear_equiv_matrix Y E (n j) (F j) (hF j)
      refine ⟨b j, G, hG, hGi, ?_⟩
      intro B x z
      rw [heq j B x]
      exact hmatrix B (continuousIntegralVector (continuousIntegers l E)
        ((b j).sections B x)) z
    choose b' G hG hGi hmatrix using hcoord
    refine ⟨r, G, hG, hGi, ?_⟩
    exact continuousSheet_coordinate_restriction l E P p M e g d t w r c b'
      (fun j y ↦ (G j y).val) hmatrix
  · have : IsEmpty Y := not_nonempty_iff.mp hY
    let b' (j : Fin d) := empty_presentation_rank Y (continuousIntegers l E) (n j) r
      ((upperStar (integralCoeff l E) (t j)).obj M) (b j)
    let G : Fin d → Y → Matrix.GeneralLinearGroup (Fin r) E := fun _ _ ↦ 1
    refine ⟨r, G, fun _ _ _ ↦ continuous_const, fun _ _ _ ↦ continuous_const, ?_⟩
    apply continuousSheet_coordinate_restriction l E P p M e g d t w r c b'
      (fun j y ↦ (G j y).val)
    intro j B x z
    exact isEmptyElim (show Y from B.hom z)

end AlgebraicGeometry.ProEtale.CondensedRing
