/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAutLift

/-!
# Automorphisms of `(ℤ/ℓⁿ)_X^r` lift to `(ℤ/ℓⁿ⁺¹)_X^r`

The rank `r` version of `WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowAutLift`. An
endomorphism of the direct sum `(ℤ/m)|_Y^r` of `r` copies of `(ℤ/m)|_Y` is a matrix of
endomorphisms of `(ℤ/m)|_Y`, i.e. of multiplications by locally constant functions: it is the
action of a matrix `A ∈ M_r(C(Y, ℤ/m))`
(`AlgebraicGeometry.ProEtale.eq_zmodAbSheafOverMatrix`), and the composition of such actions is
the product of matrices. An automorphism is thus a matrix which is pointwise invertible, and a
pointwise invertible matrix `Y → GL_r(ℤ/ℓⁿ)` lifts pointwise, hence continuously, to
`Y → GL_r(ℤ/ℓⁿ⁺¹)` (`ZMod.exists_isUnit_det_map_castHom_eq`).

Consequently, an `ℓ`-adic tower `(Gₙ)` of abelian sheaves with each `Gₙ` locally isomorphic to
`(ℤ/ℓⁿ)_X^r` has a limit which is locally isomorphic to `lim_n (ℤ/ℓⁿ)_X^r`
(`AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_limit_zmodPowAbSheafDiagramPow`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory

/-- Restriction of sheaves to a slice is additive. -/
instance GrothendieckTopology.overPullback_additive {C : Type*} [Category* C]
    (J : GrothendieckTopology C) (A : Type*) [Category* A] [Preadditive A] (X : C) :
    (J.overPullback A X).Additive where
  map_add := rfl

namespace Limits

variable {D : Type*} [Category* D] [Preadditive D]

/-- **Biproducts of cokernels are cokernels**: if each `π i` is a cokernel of `a i`, then
`biproduct.map π` is a cokernel of `biproduct.map a`. -/
noncomputable def isColimitCokernelCoforkBiproductMap {ι : Type*} {P' P Q : ι → D}
    [HasBiproduct P'] [HasBiproduct P] [HasBiproduct Q] (a : ∀ i, P' i ⟶ P i)
    (π : ∀ i, P i ⟶ Q i) (w : ∀ i, a i ≫ π i = 0)
    (h : ∀ i, IsColimit (CokernelCofork.ofπ (π i) (w i))) :
    IsColimit (CokernelCofork.ofπ (biproduct.map π) (by
      refine biproduct.hom_ext' _ _ fun i ↦ ?_
      rw [biproduct.ι_map_assoc, biproduct.ι_map, ← Category.assoc, w, zero_comp,
        comp_zero]) : CokernelCofork (biproduct.map a)) := by
  have hι {Z : D} (k : ⨁ P ⟶ Z) (hk : biproduct.map a ≫ k = 0) (i : ι) :
      a i ≫ biproduct.ι P i ≫ k = 0 := by
    rw [← biproduct.ι_map_assoc, hk, comp_zero]
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {Z} k hk ↦ biproduct.desc fun i ↦ (h i).desc (CokernelCofork.ofπ _ (hι k hk i)))
    (fun {Z} k hk ↦ biproduct.hom_ext' _ _ fun i ↦ ?_) (fun {Z} k hk m hm ↦ ?_)
  · rw [biproduct.ι_map_assoc, biproduct.ι_desc]
    exact (h i).fac (CokernelCofork.ofπ _ (hι k hk i)) WalkingParallelPair.one
  · refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [biproduct.ι_desc]
    refine Cofork.IsColimit.hom_ext (h i) ?_
    rw [Cofork.π_ofπ, ← Category.assoc, ← biproduct.ι_map, Category.assoc, hm]
    exact ((h i).fac (CokernelCofork.ofπ _ (hι k hk i)) WalkingParallelPair.one).symm

/-- **Cokernels are invariant under isomorphisms of arrows**: if `π` is a cokernel of `a`, and
`π'`, `a'` are conjugate to `π`, `a` by isomorphisms, then `π'` is a cokernel of `a'`. -/
noncomputable def isColimitCokernelCoforkOfIso {A' A B' B : D} {a : A ⟶ A} {a' : A' ⟶ A'}
    {π : A ⟶ B} {π' : A' ⟶ B'} {w : a ≫ π = 0} (w' : a' ≫ π' = 0)
    (h : IsColimit (CokernelCofork.ofπ π w)) (eA : A' ≅ A) (eB : B' ≅ B)
    (ha : a' ≫ eA.hom = eA.hom ≫ a) (hπ : π' ≫ eB.hom = eA.hom ≫ π) :
    IsColimit (CokernelCofork.ofπ π' w') := by
  have hk {Z : D} (k : A' ⟶ Z) (hk : a' ≫ k = 0) : a ≫ eA.inv ≫ k = 0 := by
    rw [← cancel_epi eA.hom, comp_zero, ← Category.assoc, ← ha, Category.assoc,
      Iso.hom_inv_id_assoc, hk]
  have hπ' : π' = eA.hom ≫ π ≫ eB.inv := by
    rw [← Category.assoc, ← hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {Z} k hk' ↦ eB.hom ≫ h.desc (CokernelCofork.ofπ _ (hk k hk')))
    (fun {Z} k hk' ↦ ?_) (fun {Z} k hk' m hm ↦ ?_)
  · rw [hπ', Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    exact (congrArg (eA.hom ≫ ·) (Cofork.IsColimit.π_desc h)).trans (Iso.hom_inv_id_assoc _ _)
  · rw [← cancel_epi eB.inv, Iso.inv_hom_id_assoc]
    refine Cofork.IsColimit.hom_ext h ?_
    rw [Cofork.IsColimit.π_desc, Cofork.π_ofπ, Cofork.π_ofπ, ← hm, hπ']
    simp

/-- Existence form of `CategoryTheory.Limits.isColimitCokernelCoforkOfIso`. -/
lemma exists_isColimit_cokernelCofork_of_iso {A' A B' B : D} {a : A ⟶ A} {a' : A' ⟶ A'}
    {π : A ⟶ B} {π' : A' ⟶ B'} {w : a ≫ π = 0} (h : IsColimit (CokernelCofork.ofπ π w))
    (eA : A' ≅ A) (eB : B' ≅ B) (ha : a' ≫ eA.hom = eA.hom ≫ a)
    (hπ : π' ≫ eB.hom = eA.hom ≫ π) :
    ∃ w' : a' ≫ π' = 0, Nonempty (IsColimit (CokernelCofork.ofπ π' w')) := by
  have w' : a' ≫ π' = 0 := by
    rw [← cancel_mono eB.hom, Category.assoc, hπ, ← Category.assoc, ha, Category.assoc, w,
      comp_zero, zero_comp]
  exact ⟨w', ⟨isColimitCokernelCoforkOfIso w' h eA eB ha hπ⟩⟩

end Limits

end CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} {f g : ι → C} [HasBiproduct f]
  [HasBiproduct g] [PreservesBiproduct f F] [PreservesBiproduct g F]
  [HasBiproduct fun i ↦ F.obj (f i)] [HasBiproduct fun i ↦ F.obj (g i)]

/-- The comparison `F (⨁ f) ≅ ⨁ (F ∘ f)` for a functor preserving the biproduct of `f`, into
any chosen biproduct of `F ∘ f` (unlike `Functor.mapBiproduct`, whose target is the biproduct
given by `hasBiproduct_of_preserves`). -/
noncomputable def mapBiproductIso (f : ι → C) [HasBiproduct f] [PreservesBiproduct f F]
    [HasBiproduct fun i ↦ F.obj (f i)] : F.obj (⨁ f) ≅ ⨁ fun i ↦ F.obj (f i) :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves F (biproduct.isBilimit f))

/-- The components of `Functor.mapBiproductIso`. -/
@[reassoc (attr := simp)]
lemma mapBiproductIso_hom_π (i : ι) :
    (F.mapBiproductIso f).hom ≫ biproduct.π _ i = F.map (biproduct.π f i) :=
  biproduct.lift_π _ _

/-- The comparison `F (⨁ f) ≅ ⨁ F f` is natural in `f`. -/
@[reassoc]
lemma map_biproductMap_comp_mapBiproductIso_hom (p : ∀ i, f i ⟶ g i) :
    F.map (biproduct.map p) ≫ (F.mapBiproductIso g).hom =
      (F.mapBiproductIso f).hom ≫ biproduct.map fun i ↦ F.map (p i) :=
  biproduct.hom_ext _ _ fun i ↦ by
    rw [Category.assoc, mapBiproductIso_hom_π, ← F.map_comp, biproduct.map_π, Category.assoc,
      biproduct.map_π, mapBiproductIso_hom_π_assoc, F.map_comp]

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {K D : Type*} [Category* K] [Category* D] [Preadditive D] [HasFiniteBiproducts D]

/-- The diagram `k ↦ ⨁_{i : ι} F k` of finite direct sums of copies of a diagram `F`. -/
@[simps]
noncomputable def biproductPow (F : K ⥤ D) (ι : Type*) [Finite ι] : K ⥤ D where
  obj k := ⨁ fun _ : ι ↦ F.obj k
  map f := biproduct.map fun _ ↦ F.map f
  map_id k := biproduct.hom_ext _ _ fun i ↦ by simp
  map_comp f g := biproduct.hom_ext _ _ fun i ↦ by simp

end CategoryTheory.Functor

namespace ZMod

/-- An element of `ℤ/ℓⁿ⁺¹` whose reduction modulo `ℓⁿ` is a unit is a unit, if `n ≥ 1`. -/
lemma isUnit_of_isUnit_castHom {l n : ℕ} [NeZero l] (hn : 0 < n) {z : ZMod (l ^ (n + 1))}
    (hz : IsUnit (castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)) z)) : IsUnit z := by
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (NeZero.ne l)⟩
  rw [← natCast_zmod_val z, map_natCast, isUnit_iff_coprime,
    Nat.coprime_pow_right_iff hn] at hz
  rwa [← natCast_zmod_val z, isUnit_iff_coprime, Nat.coprime_pow_right_iff n.succ_pos]

/-- **Invertible matrices over `ℤ/ℓⁿ` lift to invertible matrices over `ℤ/ℓⁿ⁺¹`**: for `n ≥ 1`,
any entrywise lift works, an element of `ℤ/ℓⁿ⁺¹` being a unit as soon as its reduction is; for
`n = 0`, `ℤ/ℓ⁰` is the zero ring. -/
lemma exists_isUnit_det_map_castHom_eq {l n r : ℕ} [NeZero l]
    (N : Matrix (Fin r) (Fin r) (ZMod (l ^ n))) (hN : IsUnit N.det) :
    ∃ M : Matrix (Fin r) (Fin r) (ZMod (l ^ (n + 1))),
      IsUnit M.det ∧ M.map (castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) = N := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (ZMod (l ^ 0)) := subsingleton_iff.2 (pow_zero l)
    exact ⟨1, by simp, Matrix.ext fun _ _ ↦ Subsingleton.elim _ _⟩
  · have hs := Function.surjInv_eq (castHom_surjective (pow_dvd_pow l n.le_succ) (m := l ^ n))
    refine ⟨N.map (Function.surjInv (castHom_surjective (pow_dvd_pow l n.le_succ))),
      isUnit_of_isUnit_castHom hn ?_, Matrix.ext fun i j ↦ hs _⟩
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_map]
    convert hN
    exact Matrix.ext fun i j ↦ hs _

end ZMod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X : Scheme.{u}}

/-- Multiplication by locally constant functions, as an additive map
`C(Y, ℤ/m) →+ End((ℤ/m)|_Y)`. -/
noncomputable def zmodAbSheafOverMulAddHom {m : ℕ} {Y : X.ProEt} :
    C(Y.left, ZMod m) →+ (zmodAbSheafOver m Y ⟶ zmodAbSheafOver m Y) where
  toFun := zmodAbSheafOverMul
  map_zero' := zmodAbSheafOver_hom_ext (congrArg (zmodAbSheafOver.mk _) (zero_mul 1))
  map_add' c d := zmodAbSheafOver_hom_ext (congrArg (zmodAbSheafOver.mk _) (add_mul c d 1))

/-- `zmodAbSheafOverMulAddHom` is the multiplication. -/
lemma zmodAbSheafOverMulAddHom_apply {m : ℕ} {Y : X.ProEt} (c : C(Y.left, ZMod m)) :
    zmodAbSheafOverMulAddHom c = zmodAbSheafOverMul c :=
  rfl

/-- Multiplication by `0` is `0`. -/
lemma zmodAbSheafOverMul_zero {m : ℕ} {Y : X.ProEt} :
    zmodAbSheafOverMul (0 : C(Y.left, ZMod m)) = 0 :=
  zmodAbSheafOverMulAddHom.map_zero

/-- The endomorphism of `(ℤ/m)|_Y^r` given by a matrix of locally constant functions: its
component from the `i`-th to the `j`-th summand is the multiplication by `A i j`. -/
noncomputable def zmodAbSheafOverMatrix {m r : ℕ} {Y : X.ProEt}
    (A : Matrix (Fin r) (Fin r) C(Y.left, ZMod m)) :
    (⨁ fun _ : Fin r ↦ zmodAbSheafOver m Y) ⟶ ⨁ fun _ : Fin r ↦ zmodAbSheafOver m Y :=
  biproduct.matrix fun i j ↦ zmodAbSheafOverMul (A i j)

/-- The components of `zmodAbSheafOverMatrix A` are the multiplications by the entries of `A`. -/
@[reassoc]
lemma zmodAbSheafOverMatrix_components {m r : ℕ} {Y : X.ProEt}
    (A : Matrix (Fin r) (Fin r) C(Y.left, ZMod m)) (i j : Fin r) :
    biproduct.ι _ i ≫ zmodAbSheafOverMatrix A ≫ biproduct.π _ j = zmodAbSheafOverMul (A i j) :=
  biproduct.matrix_components _ _ _

/-- Endomorphisms of a finite biproduct are determined by their components. -/
lemma biproduct_hom_ext_components {m r : ℕ} {Y : X.ProEt}
    {f g : (⨁ fun _ : Fin r ↦ zmodAbSheafOver m Y) ⟶ ⨁ fun _ : Fin r ↦ zmodAbSheafOver m Y}
    (h : ∀ i j, biproduct.ι _ i ≫ f ≫ biproduct.π _ j = biproduct.ι _ i ≫ g ≫ biproduct.π _ j) :
    f = g :=
  biproduct.hom_ext' _ _ fun i ↦ biproduct.hom_ext _ _ fun j ↦ by
    simpa only [Category.assoc] using h i j

/-- Every endomorphism of `(ℤ/m)|_Y^r` is given by a matrix of locally constant functions: the
images of the sections `1` by its components. -/
lemma eq_zmodAbSheafOverMatrix {m r : ℕ} {Y : X.ProEt}
    (f : (⨁ fun _ : Fin r ↦ zmodAbSheafOver m Y) ⟶ ⨁ fun _ : Fin r ↦ zmodAbSheafOver m Y) :
    f = zmodAbSheafOverMatrix fun i j ↦ ((biproduct.ι _ i ≫ f ≫ biproduct.π _ j).hom.app
      (op (Over.mk (𝟙 Y))) (zmodAbSheafOver.mk _ 1)).down :=
  biproduct_hom_ext_components fun i j ↦ by
    rw [zmodAbSheafOverMatrix_components]
    exact eq_zmodAbSheafOverMul _

/-- The composition of the endomorphisms given by matrices is given by their product. -/
lemma zmodAbSheafOverMatrix_comp {m r : ℕ} {Y : X.ProEt}
    (A B : Matrix (Fin r) (Fin r) C(Y.left, ZMod m)) :
    zmodAbSheafOverMatrix A ≫ zmodAbSheafOverMatrix B = zmodAbSheafOverMatrix (A * B) := by
  refine biproduct_hom_ext_components fun i k ↦ ?_
  rw [zmodAbSheafOverMatrix_components, zmodAbSheafOverMatrix, zmodAbSheafOverMatrix,
    Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π, biproduct.lift_desc,
    Matrix.mul_apply, ← zmodAbSheafOverMulAddHom_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [zmodAbSheafOverMul_comp, mul_comm]
  rfl

/-- The identity matrix gives the identity. -/
lemma zmodAbSheafOverMatrix_one {m r : ℕ} {Y : X.ProEt} :
    zmodAbSheafOverMatrix (1 : Matrix (Fin r) (Fin r) C(Y.left, ZMod m)) = 𝟙 _ := by
  refine biproduct_hom_ext_components fun i j ↦ ?_
  rw [zmodAbSheafOverMatrix_components, Category.id_comp, biproduct.ι_π]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, dite_eq_left rfl, zmodAbSheafOverMul_one, eqToHom_refl]
  · rw [Matrix.one_apply_ne h, dite_eq_right h, zmodAbSheafOverMul_zero]

/-- A matrix is determined by the endomorphism it gives. -/
lemma zmodAbSheafOverMatrix_injective {m r : ℕ} {Y : X.ProEt}
    {A B : Matrix (Fin r) (Fin r) C(Y.left, ZMod m)}
    (h : zmodAbSheafOverMatrix A = zmodAbSheafOverMatrix B) : A = B :=
  Matrix.ext fun i j ↦ zmodAbSheafOverMul_injective (by
    rw [← zmodAbSheafOverMatrix_components, h, zmodAbSheafOverMatrix_components])

/-- The reduction `(ℤ/m')|_Y ⟶ (ℤ/m)|_Y` along `m ∣ m'`. -/
noncomputable abbrev zmodAbSheafOverReduce {m m' : ℕ} (h : m ∣ m') (Y : X.ProEt) :
    zmodAbSheafOver m' Y ⟶ zmodAbSheafOver m Y :=
  ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
    ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap X (ZMod.castHom h (ZMod m)) continuous_of_discreteTopology))

/-- The reduction intertwines the multiplications by a function and by its reduction. -/
lemma zmodAbSheafOverMul_comp_reduce {m m' : ℕ} (h : m ∣ m') {Y : X.ProEt}
    (c : C(Y.left, ZMod m')) :
    zmodAbSheafOverMul c ≫ zmodAbSheafOverReduce h Y =
      zmodAbSheafOverReduce h Y ≫ zmodAbSheafOverMul
        ((⟨ZMod.castHom h (ZMod m), continuous_of_discreteTopology⟩ :
          C(ZMod m', ZMod m)).comp c) := by
  refine zmodAbSheafOver_hom_ext ?_
  refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
  exact (by rw [map_mul, map_one] :
    ZMod.castHom h (ZMod m) (c t * 1) = ZMod.castHom h (ZMod m) (c t) * ZMod.castHom h _ 1)

/-- **Pointwise invertible matrices of locally constant functions lift**: if `A * B = 1` for
matrices of continuous functions `T → ℤ/ℓⁿ`, there are matrices `Ã`, `B̃` of continuous functions
`T → ℤ/ℓⁿ⁺¹`, inverse to each other, with `Ã` reducing to `A`. The lift is chosen pointwise, by
`ZMod.exists_isUnit_det_map_castHom_eq`, continuously as `M_r(ℤ/ℓⁿ)` is discrete. -/
lemma exists_matrix_lift {T : Type*} [TopologicalSpace T] {l n r : ℕ} [NeZero l]
    {A B : Matrix (Fin r) (Fin r) C(T, ZMod (l ^ n))} (hAB : A * B = 1) :
    ∃ A' B' : Matrix (Fin r) (Fin r) C(T, ZMod (l ^ (n + 1))), A' * B' = 1 ∧ B' * A' = 1 ∧
      ∀ i j, (⟨ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)),
        continuous_of_discreteTopology⟩ : C(ZMod (l ^ (n + 1)), ZMod (l ^ n))).comp (A' i j) =
          A i j := by
  classical
  let ev (t : T) {k : ℕ} :
      Matrix (Fin r) (Fin r) C(T, ZMod k) →+* Matrix (Fin r) (Fin r) (ZMod k) :=
    (ContinuousMap.evalAlgHom ℤ (ZMod k) t).toRingHom.mapMatrix
  have hev {k : ℕ} {M M' : Matrix (Fin r) (Fin r) C(T, ZMod k)} (h : ∀ t, ev t M = ev t M') :
      M = M' :=
    Matrix.ext fun i j ↦ ContinuousMap.ext fun t ↦ congrFun (congrFun (h t) i) j
  let Am : C(T, Fin r → Fin r → ZMod (l ^ n)) :=
    ContinuousMap.pi fun i ↦ ContinuousMap.pi fun j ↦ A i j
  have hdet (t : T) : IsUnit (ev t A).det :=
    Matrix.isUnit_det_of_right_inverse (B := ev t B) (by rw [← map_mul, hAB, map_one])
  let L (N : Matrix (Fin r) (Fin r) (ZMod (l ^ n))) : Matrix (Fin r) (Fin r) (ZMod (l ^ (n + 1))) :=
    if h : IsUnit N.det then (ZMod.exists_isUnit_det_map_castHom_eq N h).choose else 1
  have hL (t : T) : IsUnit (L (ev t A)).det ∧
      (L (ev t A)).map (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) = ev t A := by
    simp only [L, dite_eq_left (hdet t)]
    exact (ZMod.exists_isUnit_det_map_castHom_eq _ (hdet t)).choose_spec
  let A' : Matrix (Fin r) (Fin r) C(T, ZMod (l ^ (n + 1))) := fun i j ↦
    ⟨fun t ↦ L (Am t) i j, (continuous_of_discreteTopology
      (f := fun N : Fin r → Fin r → ZMod (l ^ n) ↦ L N i j)).comp Am.continuous⟩
  let B' : Matrix (Fin r) (Fin r) C(T, ZMod (l ^ (n + 1))) := fun i j ↦
    ⟨fun t ↦ (L (Am t))⁻¹ i j, (continuous_of_discreteTopology
      (f := fun N : Fin r → Fin r → ZMod (l ^ n) ↦ (L N)⁻¹ i j)).comp Am.continuous⟩
  have hA' (t : T) : ev t A' = L (ev t A) := rfl
  have hB' (t : T) : ev t B' = (L (ev t A))⁻¹ := rfl
  refine ⟨A', B', hev fun t ↦ ?_, hev fun t ↦ ?_, fun i j ↦ ContinuousMap.ext fun t ↦
    congrFun (congrFun (hL t).2 i) j⟩
  · rw [map_mul, map_one, hA', hB', Matrix.mul_nonsing_inv _ (hL t).1]
  · rw [map_mul, map_one, hA', hB', Matrix.nonsing_inv_mul _ (hL t).1]

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The tower `n ↦ (ℤ/ℓⁿ)_X^r` of abelian sheaves on `X_proét`: `r` copies of
`zmodPowAbSheafDiagram`. -/
noncomputable abbrev zmodPowAbSheafDiagramPow (r : ℕ) : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (zmodPowAbSheafDiagram X l).biproductPow (Fin r)

omit [Fact l.Prime] in
/-- The objects of `zmodPowAbSheafDiagramPow` are the biproducts of those of
`zmodPowAbSheafDiagram`. -/
lemma zmodPowAbSheafDiagramPow_obj (r : ℕ) (n : ℕᵒᵖ) :
    (zmodPowAbSheafDiagramPow X l r).obj n = ⨁ fun _ : Fin r ↦ (zmodPowAbSheafDiagram X l).obj n :=
  rfl

omit [Fact l.Prime] in
/-- The transitions of `zmodPowAbSheafDiagramPow` are the biproducts of those of
`zmodPowAbSheafDiagram`. -/
lemma zmodPowAbSheafDiagramPow_map (r : ℕ) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (zmodPowAbSheafDiagramPow X l r).map f =
      biproduct.map fun _ ↦ (zmodPowAbSheafDiagram X l).map f :=
  rfl

/-- **The tower `(ℤ/ℓⁿ)_X^r` is `ℓ`-adic**: restricted to any `Y`, its transitions are cokernels
of multiplication by `ℓⁿ`, as biproducts of the transitions of `(ℤ/ℓⁿ)_X`. -/
theorem exists_isColimit_cokernelCofork_zmodPowAbSheafDiagramPow (r n : ℕ) (Y : X.ProEt) :
    ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
        ((zmodPowAbSheafDiagramPow X l r).map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)) := by
  let F := (ProEt.topology X).overPullback Ab.{u + 1} Y
  let R := zmodPowAbSheafDiagram X l
  obtain ⟨w, ⟨h⟩⟩ := exists_isColimit_cokernelCofork_zmodPowAbSheafDiagram X l n Y
  let N : ℤ := ((l ^ n : ℕ) : ℤ)
  have h' := isColimitCokernelCoforkBiproductMap (fun _ : Fin r ↦ N • 𝟙 _)
    (fun _ : Fin r ↦ F.map (R.map (homOfLE n.le_succ).op)) (fun _ ↦ w) (fun _ ↦ h)
  have hN {A : Fin r → Sheaf ((ProEt.topology X).over Y) Ab.{u + 1}} :
      (biproduct.map fun i ↦ N • 𝟙 (A i)) = N • 𝟙 _ :=
    biproduct.hom_ext _ _ fun i ↦ by
      rw [biproduct.map_π, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.id_comp,
        Category.comp_id]
  rw [zmodPowAbSheafDiagramPow_map]
  refine exists_isColimit_cokernelCofork_of_iso
    (a' := N • 𝟙 (F.obj (⨁ fun _ : Fin r ↦ R.obj (op (n + 1))))) h' (F.mapBiproductIso _)
    (F.mapBiproductIso _) ?_
    (F.map_biproductMap_comp_mapBiproductIso_hom _)
  rw [hN, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]

/-- **Automorphisms of `(ℤ/ℓⁿ)|_Y^r` lift to `(ℤ/ℓⁿ⁺¹)|_Y^r`**: an automorphism of `(ℤ/ℓⁿ)|_Y^r`
is given by a pointwise invertible matrix `A` of locally constant functions, and a pointwise
invertible lift of `A` gives an automorphism of `(ℤ/ℓⁿ⁺¹)|_Y^r` lifting it along the
reduction. -/
theorem exists_iso_hom_comp_zmodPowAbSheafDiagramPow_map (r n : ℕ) (Y : X.ProEt)
    (α : ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagramPow X l r).obj (op n)) ≅
      ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagramPow X l r).obj (op n))) :
    ∃ β : ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagramPow X l r).obj (op (n + 1))) ≅
      ((ProEt.topology X).overPullback Ab.{u + 1} Y).obj
        ((zmodPowAbSheafDiagramPow X l r).obj (op (n + 1))),
      β.hom ≫ ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
          ((zmodPowAbSheafDiagramPow X l r).map (homOfLE n.le_succ).op) =
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map
          ((zmodPowAbSheafDiagramPow X l r).map (homOfLE n.le_succ).op) ≫ α.hom := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  let F := (ProEt.topology X).overPullback Ab.{u + 1} Y
  let R := zmodPowAbSheafDiagram X l
  have hdvd : l ^ n ∣ l ^ (n + 1) := pow_dvd_pow l n.le_succ
  let e : F.obj ((zmodPowAbSheafDiagramPow X l r).obj (op n)) ≅
      ⨁ fun _ : Fin r ↦ zmodAbSheafOver (l ^ n) Y :=
    F.mapBiproductIso fun _ : Fin r ↦ R.obj (op n)
  let e' : F.obj ((zmodPowAbSheafDiagramPow X l r).obj (op (n + 1))) ≅
      ⨁ fun _ : Fin r ↦ zmodAbSheafOver (l ^ (n + 1)) Y :=
    F.mapBiproductIso fun _ : Fin r ↦ R.obj (op (n + 1))
  have hM : F.map ((zmodPowAbSheafDiagramPow X l r).map (homOfLE n.le_succ).op) ≫ e.hom =
      e'.hom ≫ biproduct.map fun _ ↦ zmodAbSheafOverReduce hdvd Y := by
    rw [zmodPowAbSheafDiagramPow_map]
    exact F.map_biproductMap_comp_mapBiproductIso_hom _
  let α' := e.symm ≪≫ α ≪≫ e
  let A : Matrix (Fin r) (Fin r) C(Y.left, ZMod (l ^ n)) := fun i j ↦
    ((biproduct.ι _ i ≫ α'.hom ≫ biproduct.π _ j).hom.app (op (Over.mk (𝟙 Y)))
      (zmodAbSheafOver.mk _ 1)).down
  let B : Matrix (Fin r) (Fin r) C(Y.left, ZMod (l ^ n)) := fun i j ↦
    ((biproduct.ι _ i ≫ α'.inv ≫ biproduct.π _ j).hom.app (op (Over.mk (𝟙 Y)))
      (zmodAbSheafOver.mk _ 1)).down
  have hA : α'.hom = zmodAbSheafOverMatrix A := eq_zmodAbSheafOverMatrix _
  have hB : α'.inv = zmodAbSheafOverMatrix B := eq_zmodAbSheafOverMatrix _
  have hAB : A * B = 1 := zmodAbSheafOverMatrix_injective (by
    rw [← zmodAbSheafOverMatrix_comp, ← hA, ← hB, α'.hom_inv_id]
    exact zmodAbSheafOverMatrix_one.symm)
  obtain ⟨A', B', hAB', hBA', hA'⟩ := exists_matrix_lift hAB
  let β' : (⨁ fun _ : Fin r ↦ zmodAbSheafOver (l ^ (n + 1)) Y) ≅
      ⨁ fun _ : Fin r ↦ zmodAbSheafOver (l ^ (n + 1)) Y :=
    { hom := zmodAbSheafOverMatrix A'
      inv := zmodAbSheafOverMatrix B'
      hom_inv_id := by rw [zmodAbSheafOverMatrix_comp, hAB', zmodAbSheafOverMatrix_one]
      inv_hom_id := by rw [zmodAbSheafOverMatrix_comp, hBA', zmodAbSheafOverMatrix_one] }
  have hβ' : zmodAbSheafOverMatrix A' ≫ biproduct.map (fun _ ↦ zmodAbSheafOverReduce hdvd Y) =
      biproduct.map (fun _ ↦ zmodAbSheafOverReduce hdvd Y) ≫ α'.hom := by
    rw [hA]
    refine biproduct.hom_ext' _ _ fun i ↦ biproduct.hom_ext _ _ fun j ↦ ?_
    simp only [Category.assoc, biproduct.map_π, biproduct.ι_map_assoc]
    rw [zmodAbSheafOverMatrix_components_assoc, zmodAbSheafOverMatrix_components, ← hA' i j]
    exact zmodAbSheafOverMul_comp_reduce _ _
  refine ⟨e' ≪≫ β' ≪≫ e'.symm, ?_⟩
  rw [← cancel_mono e.hom, Category.assoc, hM, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  refine (congrArg (e'.hom ≫ ·) hβ').trans ?_
  simp only [α', Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← reassoc_of% hM, Iso.hom_inv_id_assoc]


/-- **An `ℓ`-adic tower of sheaves locally isomorphic to `(ℤ/ℓⁿ)_X^r` has a lattice which is
locally `lim_n (ℤ/ℓⁿ)_X^r`.** Let `(Gₙ)` be a tower of pro-étale abelian sheaves whose
transitions are, locally, cokernels of `ℓⁿ` (i.e. `Gₙ₊₁/ℓⁿ ≅ Gₙ`), with each `Gₙ` locally
isomorphic to `(ℤ/ℓⁿ)_X^r`. Then `lim Gₙ` is isomorphic to `lim_n (ℤ/ℓⁿ)_X^r` over the members
of a pro-étale cover of any object. -/
theorem exists_cover_nonempty_iso_limit_zmodPowAbSheafDiagramPow (r : ℕ)
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1})
    (hG : ∀ (n : ℕ) (Y : X.ProEt), ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫
        ((ProEt.topology X).overPullback Ab.{u + 1} Y).map (G.map (homOfLE n.le_succ).op) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (hloc : ∀ (n : ℕ) (V : X.ProEt), ∃ S ∈ ProEt.topology X V,
      ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
        Nonempty ((isoPresheaf ((zmodPowAbSheafDiagramPow X l r).obj (op n))
          (G.obj (op n))).obj (op Y)))
    (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      Sieve.ofArrows W f ∈ ProEt.topology X V ∧
      ∀ i, Nonempty (((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj (limit G) ≅
        ((ProEt.topology X).overPullback Ab.{u + 1} (W i)).obj
          (limit (zmodPowAbSheafDiagramPow X l r))) := by
  obtain ⟨ι, W, f, hcov, h⟩ :=
    exists_cover_nonempty_iso_overPullback_limit_of_isColimit_cokernelCofork
      (zmodPowAbSheafDiagramPow X l r) G (fun n ↦ ((l ^ n : ℕ) : ℤ))
      (exists_isColimit_cokernelCofork_zmodPowAbSheafDiagramPow X l r) hG hloc
      (fun n Y _ ↦ ⟨⊤, (ProEt.topology X).top_mem Y, fun Z _ _ ↦
        exists_iso_hom_comp_zmodPowAbSheafDiagramPow_map X l r n Z _⟩) V
  exact ⟨ι, W, f, hcov, fun i ↦ ⟨(h i).some.symm⟩⟩

end AlgebraicGeometry.ProEtale
