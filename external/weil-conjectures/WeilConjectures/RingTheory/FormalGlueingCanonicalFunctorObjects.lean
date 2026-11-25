/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
import WeilConjectures.AlgebraicGeometry.FormalGlueingCanonicalMaps

@[expose] public section

universe u v w

open CategoryTheory
namespace FormalGlueing

private theorem canonical_piece_eq {R : Type u} [CommRing R]
    (e : R) (M : ModuleCat.{w} R) :
    piece e (ModuleCat.of (Localization.Away e) (LocalizedModule.Away e M)) =
      localize e M := by
  have hm : Module.compHom (LocalizedModule.Away e M)
      (algebraMap R (Localization.Away e)) =
      (inferInstance : Module R (LocalizedModule.Away e M)) := by
    apply Module.ext'
    intro r x
    exact algebraMap_smul (Localization.Away e) r x
  change @ModuleCat.of R _ (LocalizedModule.Away e M) _
    (Module.compHom _ (algebraMap R (Localization.Away e))) = _
  rw [hm]

private theorem canonical_alpha {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (e : R)
    (M P : ModuleCat.{max u w} R) (h : P = localize e M) :
    ∃ a : localize e (restrict φ (extend φ M)) ≃ₗ[R] restrict φ (extend φ P),
      (∀ (s : S) (x : localize e (restrict φ (extend φ M))),
        a ((localizedSModule φ e (extend φ M)).smul s x) =
          (s • (a x : extend φ P))) ∧
      HEq a.toLinearMap (compare φ e M) := by
  subst P
  let : Algebra R S := φ.toAlgebra
  exact ⟨LinearEquiv.ofBijective (compare φ e M)
    (compare_properties φ M e).2.2.2.2, compare_smul φ e M, HEq.rfl⟩

private theorem canonical_overlap {R : Type u} [CommRing R]
    (e d : R) (M P Q : ModuleCat.{max u w} R)
    (hP : P = localize e M) (hQ : Q = localize d M) :
    ∃ b : localize d P ≃ₗ[R] localize e Q,
      HEq b.toLinearMap (swap e d M) := by
  subst P
  subst Q
  have hs := swap_properties M e d
  exact ⟨LinearEquiv.ofBijective (swap e d M)
    ⟨Function.LeftInverse.injective
        (fun x ↦ LinearMap.congr_fun hs.2.2.2.2.1 x),
      Function.RightInverse.surjective
        (fun x ↦ LinearMap.congr_fun hs.2.2.2.2.2 x)⟩, HEq.rfl⟩

private theorem outer_bijective {R : Type u} [CommRing R]
    (M : ModuleCat.{w} R) (e : R) :
    Function.Bijective (fun x : localize e M ↦ e • x) :=
  (Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers e) M)
      (⟨e, ⟨1, pow_one e⟩⟩ : Submonoid.powers e))

private theorem local_bijective {R : Type u} [CommRing R]
    (M : ModuleCat.{w} R) (e r : R)
    (hr : Function.Bijective (fun x : M ↦ r • x)) :
    Function.Bijective (fun x : localize e M ↦ r • x) := by
  let h := algebraMap R (Module.End R M) r
  have heq : localMap e h = algebraMap R (Module.End R (localize e M)) r := by
    ext x
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      simp [localMap, h, IsLocalizedModule.map_LocalizedModules,
        Module.algebraMap_end_apply, LocalizedModule.smul'_mk]
  rw [show (fun x : localize e M ↦ r • x) = localMap e h from
    congrArg DFunLike.coe heq.symm]
  exact ⟨IsLocalizedModule.map_injective _ _ _ h hr.1,
    IsLocalizedModule.map_surjective _ _ _ h hr.2⟩

private theorem local_ext {R : Type u} [CommRing R]
    (M : ModuleCat.{w} R) (e : R) {N : Type v} [AddCommGroup N] [Module R N]
    (he : Function.Bijective (fun x : N ↦ e • x))
    {h k : localize e M →ₗ[R] N}
    (hk : ∀ m : M, h (LocalizedModule.mk m 1) = k (LocalizedModule.mk m 1)) :
    h = k := by
  apply IsLocalizedModule.ext (Submonoid.powers e)
    (LocalizedModule.mkLinearMap _ M)
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).mpr he).pow n
  · exact LinearMap.ext hk

private theorem local_map_one {R : Type u} [CommRing R]
    (e : R) {M N : ModuleCat.{w} R} (h : M →ₗ[R] N) (m : M) :
    localMap e h (LocalizedModule.mk m 1) = LocalizedModule.mk (h m) 1 :=
  IsLocalizedModule.map_LocalizedModules _ h m 1

private theorem swap_one {R : Type u} [CommRing R]
    (e d : R) (M : ModuleCat.{w} R) (m : M) :
    swap e d M (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 :=
  (exists_swap e d M).exists.choose_spec m

private theorem canonical_cocycle {R : Type u} [CommRing R]
    (e d c : R) (M : ModuleCat.{max u w} R) :
    (localMap e (swap d c M)).comp
        ((swap e c (localize d M)).comp (localMap c (swap e d M))) =
      (swap e d (localize c M)).comp
        ((localMap d (swap e c M)).comp (swap d c (localize e M))) := by
  have he := outer_bijective (localize d (localize c M)) e
  have hd := local_bijective (localize d (localize c M)) e d
    (outer_bijective (localize c M) d)
  have hc := local_bijective (localize d (localize c M)) e c
    (local_bijective (localize c M) d c (outer_bijective M c))
  apply local_ext (localize d (localize e M)) c hc
  intro x
  have hh :
      (((localMap e (swap d c M)).comp
        ((swap e c (localize d M)).comp (localMap c (swap e d M)))).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers c) (localize d (localize e M)))) =
      (((swap e d (localize c M)).comp
        ((localMap d (swap e c M)).comp (swap d c (localize e M)))).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers c) (localize d (localize e M)))) := by
    apply local_ext (localize e M) d hd
    intro y
    have hh' :
        (((localMap e (swap d c M)).comp
          ((swap e c (localize d M)).comp (localMap c (swap e d M)))).comp
          ((LocalizedModule.mkLinearMap (Submonoid.powers c) _).comp
            (LocalizedModule.mkLinearMap (Submonoid.powers d) _))) =
        (((swap e d (localize c M)).comp
          ((localMap d (swap e c M)).comp (swap d c (localize e M)))).comp
          ((LocalizedModule.mkLinearMap (Submonoid.powers c) _).comp
            (LocalizedModule.mkLinearMap (Submonoid.powers d) _))) := by
      apply local_ext M e he
      intro m
      simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
      rw [local_map_one c (swap e d M), swap_one e d M,
        swap_one e c (localize d M), local_map_one e (swap d c M), swap_one d c M,
        swap_one d c (localize e M), local_map_one d (swap e c M), swap_one e c M,
        swap_one e d (localize c M)]
    exact LinearMap.congr_fun hh' y
  exact LinearMap.congr_fun hh x

private theorem extend_bijective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S)
    (M : ModuleCat.{w} R) (r : R)
    (hr : Function.Bijective (fun x : M ↦ r • x)) :
    Function.Bijective (fun x : restrict φ (extend φ M) ↦ r • x) := by
  let : Algebra R S := φ.toAlgebra
  let h := algebraMap R (Module.End R M) r
  let E := LinearEquiv.ofBijective h hr
  have heq : (fun x : restrict φ (extend φ M) ↦ r • x) =
      (E.baseChange R S : TensorProduct R S M → TensorProduct R S M) := by
    funext x
    change TensorProduct R S M at x
    change (φ r) • (x : TensorProduct R S M) = (E.baseChange R S) x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      simp only [LinearEquiv.baseChange_tmul]
      change (φ r) • (TensorProduct.tmul R s m) = TensorProduct.tmul R s (r • m)
      change (algebraMap R S r) • (TensorProduct.tmul R s m) = TensorProduct.tmul R s (r • m)
      rw [algebraMap_smul, TensorProduct.tmul_smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  rw [heq]
  exact (E.baseChange R S).bijective

private theorem compare_tensor_one {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (e : R)
    (M : ModuleCat.{w} R) (s : S) (m : M) :
    letI : Algebra R S := φ.toAlgebra
    compare φ e M (LocalizedModule.mk
      (show restrict φ (extend φ M) from TensorProduct.tmul R s m) 1) =
      (show restrict φ (extend φ (localize e M)) from
        TensorProduct.tmul R s (LocalizedModule.mk m 1)) := by
  let : Algebra R S := φ.toAlgebra
  have h := LinearMap.congr_fun (exists_compare φ e M).exists.choose_spec
    (show restrict φ (extend φ M) from TensorProduct.tmul R s m)
  change compare φ e M (LocalizedModule.mk (TensorProduct.tmul R s m) 1) =
    TensorProduct.tmul R s (LocalizedModule.mk m 1) at h
  exact h

private theorem extend_tensor {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : ModuleCat.{w} R} (h : M →ₗ[R] N) (s : S) (m : M) :
    letI : Algebra R S := φ.toAlgebra
    extendMapR φ h (show restrict φ (extend φ M) from TensorProduct.tmul R s m) =
      (show restrict φ (extend φ N) from TensorProduct.tmul R s (h m)) := by
  let : Algebra R S := φ.toAlgebra
  rfl

private theorem canonical_square {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (e d : R)
    (M : ModuleCat.{max u v w} R) :
    (extendMapR φ (swap e d M)).comp
        ((compare φ d (localize e M)).comp (localMap d (compare φ e M))) =
      (compare φ e (localize d M)).comp
        ((localMap e (compare φ d M)).comp (swap e d (restrict φ (extend φ M)))) := by
  let : Algebra R S := φ.toAlgebra
  have he := extend_bijective φ (localize e (localize d M)) e
    (outer_bijective (localize d M) e)
  have hd := extend_bijective φ (localize e (localize d M)) d
    (local_bijective (localize d M) e d (outer_bijective M d))
  apply local_ext (localize e (restrict φ (extend φ M))) d hd
  intro x
  have hh :
      (((extendMapR φ (swap e d M)).comp
        ((compare φ d (localize e M)).comp (localMap d (compare φ e M)))).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers d) _)) =
      (((compare φ e (localize d M)).comp
        ((localMap e (compare φ d M)).comp (swap e d (restrict φ (extend φ M))))).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers d) _)) := by
    apply local_ext (restrict φ (extend φ M)) e he
    intro y
    change TensorProduct R S M at y
    induction y using TensorProduct.inductionOn with
    | tmul s m =>
      simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
      rw [local_map_one d (compare φ e M), compare_tensor_one φ e M,
        compare_tensor_one φ d (localize e M), extend_tensor φ,
        swap_one e d M, swap_one e d (restrict φ (extend φ M)),
        local_map_one e (compare φ d M), compare_tensor_one φ d M,
        compare_tensor_one φ e (localize d M)]
    | add x y hx hy =>
      have hm : LocalizedModule.mk (show restrict φ (extend φ M) from x + y)
          (1 : Submonoid.powers e) =
          LocalizedModule.mk (show restrict φ (extend φ M) from x) 1 +
            LocalizedModule.mk (show restrict φ (extend φ M) from y) 1 := by
        rw [LocalizedModule.mk_add_mk]
        simp only [one_smul, one_mul]
      rw [hm]
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact LinearMap.congr_fun hh x

private theorem transported_square {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (e d : R)
    (M P Q : ModuleCat.{max u v w} R)
    (hP : P = localize e M) (hQ : Q = localize d M)
    (a : localize e (restrict φ (extend φ M)) ≃ₗ[R] restrict φ (extend φ P))
    (a' : localize d (restrict φ (extend φ M)) ≃ₗ[R] restrict φ (extend φ Q))
    (b : localize d P ≃ₗ[R] localize e Q)
    (ha : HEq a.toLinearMap (compare φ e M))
    (ha' : HEq a'.toLinearMap (compare φ d M))
    (hb : HEq b.toLinearMap (swap e d M)) :
    (extendMapR φ b.toLinearMap).comp
        ((compare φ d P).comp (localMap d a.toLinearMap)) =
      (compare φ e Q).comp
        ((localMap e a'.toLinearMap).comp (swap e d (restrict φ (extend φ M)))) := by
  subst P
  subst Q
  rw [eq_of_heq ha, eq_of_heq ha', eq_of_heq hb]
  exact canonical_square.{u, v, w} φ e d M

private theorem transported_cocycle {R : Type u} [CommRing R]
    (e d c : R) (M P Q T : ModuleCat.{max u w} R)
    (hP : P = localize e M) (hQ : Q = localize d M) (hT : T = localize c M)
    (bPQ : localize d P ≃ₗ[R] localize e Q)
    (bQT : localize c Q ≃ₗ[R] localize d T)
    (bPT : localize c P ≃ₗ[R] localize e T)
    (hbPQ : HEq bPQ.toLinearMap (swap e d M))
    (hbQT : HEq bQT.toLinearMap (swap d c M))
    (hbPT : HEq bPT.toLinearMap (swap e c M)) :
    (localMap e bQT.toLinearMap).comp
        ((swap e c Q).comp (localMap c bPQ.toLinearMap)) =
      (swap e d T).comp ((localMap d bPT.toLinearMap).comp (swap d c P)) := by
  subst P
  subst Q
  subst T
  rw [eq_of_heq hbPQ, eq_of_heq hbQT, eq_of_heq hbPT]
  exact canonical_cocycle e d c M

/-- The canonical glueing object of a single module; no morphisms are asserted here.
Source: Stacks Project, More on Algebra, Remark 05EL, construction of `Can`.
(blueprint: lem-weil-pbc-formal-glueing-canonical-functor-objects).
Proof: take the prime module to be S tensor M and chart i to be M localized at f i,
with its canonical module structure over R localized at f i. Restricting the chart
back to R gives the original localized R-module: algebraMap_smul identifies the
actions, and the underlying additive groups coincide. Transport the comparison and
swap maps along these bundled-module equalities. The compare_properties theorem
makes comparison bijective, and swap_properties gives inverse swaps. Use these to
form linear equivalences; compare_smul supplies alpha_smul. For the square, both
paths send a pure tensor fraction with denominators f i and f j to the tensor of
that element with the denominators interchanged. Tensor induction and localization
induction extend this equality to every element. For the cocycle, every element is
a threefold fraction; both paths reverse the order of its three denominators.
The fraction formulas in swap_properties prove equality. Thus these fields satisfy
Data.square and Data.cocycle. All remaining fields are proofs. This works also for
an empty chart family, zero denominators, and the zero module. -/
theorem exists_canonical_functor_objects {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (M : ModuleCat.{max u v w} R) :
    ∃ X : Data.{u, v, max u v w} φ f,
      X.M' = extend φ M ∧
      (∀ i : Fin t, X.M i =
        ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
      (∀ i : Fin t, HEq (X.alpha i).toLinearMap (compare φ (f i) M)) ∧
      (∀ i j : Fin t, HEq (X.alpha_overlap i j).toLinearMap (swap (f i) (f j) M)) := by
  classical
  let : Algebra R S := φ.toAlgebra
  let A : ModuleCat S := extend φ M
  let C : ∀ i : Fin t, ModuleCat (Localization.Away (f i)) :=
    fun i ↦ ModuleCat.of (Localization.Away (f i))
      (LocalizedModule.Away (f i) M)
  have ha (i : Fin t) := canonical_alpha.{u, v, max v w} φ (f i) M (piece (f i) (C i))
    (canonical_piece_eq (f i) M)
  choose a ha_smul ha_eq using ha
  have hb (i j : Fin t) := canonical_overlap.{u, max v w} (f i) (f j) M
    (piece (f i) (C i)) (piece (f j) (C j))
    (canonical_piece_eq (f i) M) (canonical_piece_eq (f j) M)
  choose b hb_eq using hb
  let X : Data φ f := {
    M' := A
    M := C
    alpha := a
    alpha_smul := ha_smul
    alpha_overlap := b
    square := by
      intro i j
      exact transported_square.{u, v, w} φ (f i) (f j) M
        (piece (f i) (C i)) (piece (f j) (C j))
        (canonical_piece_eq (f i) M) (canonical_piece_eq (f j) M)
        (a i) (a j) (b i j) (ha_eq i) (ha_eq j) (hb_eq i j)
    cocycle := by
      intro i j k
      exact transported_cocycle.{u, max v w} (f i) (f j) (f k) M
        (piece (f i) (C i)) (piece (f j) (C j)) (piece (f k) (C k))
        (canonical_piece_eq (f i) M) (canonical_piece_eq (f j) M)
        (canonical_piece_eq (f k) M)
        (b i j) (b j k) (b i k) (hb_eq i j) (hb_eq j k) (hb_eq i k) }
  refine ⟨X, rfl, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    exact ha_eq i
  · intro i j
    exact hb_eq i j

end FormalGlueing
