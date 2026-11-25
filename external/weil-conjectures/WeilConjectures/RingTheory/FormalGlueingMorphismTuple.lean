/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
public import WeilConjectures.RingTheory.CoverModuleExact
import WeilConjectures.AlgebraicGeometry.FormalGlueingCanonicalMaps

/-!
# Compatible tuples induced by canonical morphisms

Source: Stacks Project, More on Algebra, Lemmas 05EK and 05EM.
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace FormalGlueing

private theorem canonical_piece_eq {R : Type u} [CommRing R] (a : R)
    (M : ModuleCat.{w} R) :
    piece a (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) =
      localize a M := by
  have hm : Module.compHom (LocalizedModule.Away a M)
      (algebraMap R (Localization.Away a)) =
      (inferInstance : Module R (LocalizedModule.Away a M)) := by
    apply Module.ext'
    intro r x
    exact algebraMap_smul (Localization.Away a) r x
  change @ModuleCat.of R _ _ _ (Module.compHom _ _) = _
  rw [hm]

private theorem prime_compat_transport {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (a : R)
    (M N : ModuleCat.{max u v w} R)
    (A B : ModuleCat.{max u v w} S) (C D : ModuleCat.{max u v w} R)
    (hA : A = extend φ M) (hB : B = extend φ N)
    (hC : C = localize a M) (hD : D = localize a N)
    (α : localize a (restrict φ A) →ₗ[R] restrict φ (extend φ C))
    (β : localize a (restrict φ B) →ₗ[R] restrict φ (extend φ D))
    (q : A →ₗ[S] B) (d : C →ₗ[R] D)
    (p : extend φ M →ₗ[S] extend φ N)
    (c : localize a M →ₗ[R] localize a N)
    (hα : HEq α (compare φ a M)) (hβ : HEq β (compare φ a N))
    (hq : HEq q p) (hd : HEq d c)
    (h : β.comp (localMap a (restrictMap φ q)) = (extendMapR φ d).comp α) :
    (compare φ a N).comp (localMap a (restrictMap φ p)) =
      (extendMapR φ c).comp (compare φ a M) := by
  subst A B C D
  cases eq_of_heq hα
  cases eq_of_heq hβ
  cases eq_of_heq hq
  cases eq_of_heq hd
  exact h

private theorem chart_compat_transport {R : Type u} [CommRing R] (a b : R)
    (M N : ModuleCat.{max u w} R)
    (A B C D : ModuleCat.{max u w} R)
    (hA : A = localize a M) (hB : B = localize a N)
    (hC : C = localize b M) (hD : D = localize b N)
    (α : localize b A →ₗ[R] localize a C)
    (β : localize b B →ₗ[R] localize a D)
    (d : A →ₗ[R] B) (e : C →ₗ[R] D)
    (c : localize a M →ₗ[R] localize a N)
    (c' : localize b M →ₗ[R] localize b N)
    (hα : HEq α (swap a b M)) (hβ : HEq β (swap a b N))
    (hd : HEq d c) (he : HEq e c')
    (h : β.comp (localMap b d) = (localMap a e).comp α) :
    (swap a b N).comp (localMap b c) = (localMap a c').comp (swap a b M) := by
  subst A B C D
  cases eq_of_heq hα
  cases eq_of_heq hβ
  cases eq_of_heq hd
  cases eq_of_heq he
  exact h

private theorem compare_eta {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (a : R) (N : ModuleCat.{w} R) :
    letI : Algebra R S := φ.toAlgebra
    ∀ n : localize a N,
      compare φ a N (IsLocalizedModule.map (Submonoid.powers a)
        (LocalizedModule.mkLinearMap _ N)
        (LocalizedModule.mkLinearMap _ (S ⊗[R] N))
        (TensorProduct.mk R S N 1) n) = (1 : S) ⊗ₜ[R] n := by
  let : Algebra R S := φ.toAlgebra
  intro n
  induction n using LocalizedModule.induction_on with
  | _ x d =>
    obtain ⟨k, hk⟩ := d.2
    have hd : d = (⟨a ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers a) := Subtype.ext hk.symm
    subst d
    rw [IsLocalizedModule.map_LocalizedModules]
    exact (compare_properties φ N a).2.1 x 1 k

private theorem overlap_of_swap {R : Type u} [CommRing R]
    (N : ModuleCat.{w} R) (a b : R)
    (x : localize a N) (y : localize b N)
    (h : swap a b N (LocalizedModule.mk x 1) = LocalizedModule.mk y 1) :
    IsLocalizedModule.lift (Submonoid.powers a)
      (LocalizedModule.mkLinearMap _ N)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)
      (RingTheory.localizationAway_map_units_of_dvd a (a * b) (dvd_mul_right a b)) x =
    IsLocalizedModule.lift (Submonoid.powers b)
      (LocalizedModule.mkLinearMap _ N)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)
      (RingTheory.localizationAway_map_units_of_dvd b (a * b) (dvd_mul_left b a)) y := by
  let la := LocalizedModule.mkLinearMap (Submonoid.powers a) N
  let lb := LocalizedModule.mkLinearMap (Submonoid.powers b) N
  let lab := LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N
  let ua := RingTheory.localizationAway_map_units_of_dvd (M := N) a (a * b)
    (dvd_mul_right a b)
  let ub := RingTheory.localizationAway_map_units_of_dvd (M := N) b (a * b)
    (dvd_mul_left b a)
  let ra := IsLocalizedModule.lift (Submonoid.powers a) la lab ua
  let rb := IsLocalizedModule.lift (Submonoid.powers b) lb lab ub
  let lab' := LocalizedModule.mkLinearMap (Submonoid.powers b) (localize a N)
  let lba' := LocalizedModule.mkLinearMap (Submonoid.powers a) (localize b N)
  let rab := IsLocalizedModule.lift (Submonoid.powers b) lab' ra ub
  let rba := IsLocalizedModule.lift (Submonoid.powers a) lba' rb ua
  have heq : rba.comp (swap a b N) = rab := by
    apply IsLocalizedModule.ext (Submonoid.powers b) lab' ub
    apply IsLocalizedModule.ext (Submonoid.powers a) la ua
    ext n
    simp only [LinearMap.comp_apply]
    have hs : swap a b N (lab' (la n)) = lba' (lb n) :=
      (exists_swap a b N).exists.choose_spec n
    rw [hs]
    change rba (lba' (lb n)) = rab (lab' (la n))
    rw [IsLocalizedModule.lift_apply, IsLocalizedModule.lift_apply,
      IsLocalizedModule.lift_apply, IsLocalizedModule.lift_apply]
  have hh := congrArg rba h
  change (rba.comp (swap a b N)) (lab' x) = rba (lba' y) at hh
  rw [heq] at hh
  simpa only [rab, rba, IsLocalizedModule.lift_apply] using hh

/-- The image of an input under the components of a canonical morphism is a compatible
formal glueing tuple. This is a kernel calculation, with no flatness assumption and no
assertion of existence of a preimage in N.
Source: Stacks Project, More on Algebra, Remark 05EL and the complex preceding Lemma 05EK.
(blueprint: lem-weil-pbc-formal-glueing-morphism-tuple).
Proof: transport the prime and chart components along the given object equalities.
Evaluate prime compatibility on (1 tensor m)/1. The canonical comparison formula
identifies the two sides with the comparison of the localized prime value and
1 tensor c_i(m/1). The comparison is injective, so the prime differences vanish.
Evaluate overlap compatibility on (m/1)/1. The canonical swap fixes this double
localization of m, so swap(n_i/1) = n_j/1 for n_i = c_i(m/1).
Write n_i = x/f_i^a and n_j = y/f_j^b. The swap formula identifies the left side
with (x/1)/f_i^a. Clearing the outer f_i denominator gives a power f_i^c
annihilating x/1 - f_i^a y/f_j^b in N_fj. Clearing the inner f_j denominator gives
a power f_j^d annihilating f_i^c(f_j^b x - f_i^a y) in N.
The difference of the images in N_(fi*fj) has numerator
f_i^b f_j^a(f_j^b x - f_i^a y) and denominator (f_i*f_j)^(a+b).
Multiplication by (f_i*f_j)^(c+d) annihilates that numerator. Thus all overlap
differences vanish as well. Extensionality of products and functions gives beta = 0.
Empty chart families, zero denominators and zero modules are included, since this
argument uses localized equality criteria and never cancels a scalar in N. -/
theorem canonical_tuple_compatible {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (M N : ModuleCat.{max u v w} R)
    (X Y : Data.{u, v, max u v w} φ f)
    (hX : X.M' = extend φ M ∧
      (∀ i, X.M i = ModuleCat.of (Localization.Away (f i))
        (LocalizedModule.Away (f i) M)) ∧
      (∀ i, HEq (X.alpha i).toLinearMap (compare φ (f i) M)) ∧
      (∀ i j, HEq (X.alpha_overlap i j).toLinearMap (swap (f i) (f j) M)))
    (hY : Y.M' = extend φ N ∧
      (∀ i, Y.M i = ModuleCat.of (Localization.Away (f i))
        (LocalizedModule.Away (f i) N)) ∧
      (∀ i, HEq (Y.alpha i).toLinearMap (compare φ (f i) N)) ∧
      (∀ i j, HEq (Y.alpha_overlap i j).toLinearMap (swap (f i) (f j) N)))
    (z : X ⟶ Y)
    (p : extend φ M →ₗ[S] extend φ N)
    (c : ∀ i, localize (f i) M →ₗ[R] localize (f i) N)
    (hp : HEq z.prime p) (hc : ∀ i, HEq (z.chart i) (c i)) :
    letI : Algebra R S := φ.toAlgebra
    let η : N →ₗ[R] S ⊗[R] N := TensorProduct.mk R S N 1
    let ρ := fun (a h : R) (ha : a ∣ h) ↦
      IsLocalizedModule.lift (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) N)
        (LocalizedModule.mkLinearMap (Submonoid.powers h) N)
        (RingTheory.localizationAway_map_units_of_dvd (M := N) a h ha)
    let β : (S ⊗[R] N) × (∀ i : Fin t, LocalizedModule.Away (f i) N) →
        (∀ i : Fin t, LocalizedModule.Away (f i) (S ⊗[R] N)) ×
          (∀ i j : Fin t, LocalizedModule.Away (f i * f j) N) :=
      fun q ↦
        (fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] N) q.1 -
          IsLocalizedModule.map (Submonoid.powers (f i))
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N)
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] N)) η (q.2 i),
         fun i j ↦ ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (q.2 i) -
          ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (q.2 j))
    ∀ m : M, β (p ((1 : S) ⊗ₜ[R] m), fun i ↦ c i (LocalizedModule.mk m 1)) = 0 := by
  let : Algebra R S := φ.toAlgebra
  have hpieceX (i : Fin t) : piece (f i) (X.M i) = localize (f i) M := by
    rw [hX.2.1 i]
    exact canonical_piece_eq (f i) M
  have hpieceY (i : Fin t) : piece (f i) (Y.M i) = localize (f i) N := by
    rw [hY.2.1 i]
    exact canonical_piece_eq (f i) N
  have hprime (i : Fin t) := prime_compat_transport.{u, v, w} φ (f i) M N
    X.M' Y.M' (piece (f i) (X.M i)) (piece (f i) (Y.M i))
    hX.1 hY.1 (hpieceX i) (hpieceY i) (X.alpha i).toLinearMap
    (Y.alpha i).toLinearMap z.prime (z.chart i) p (c i)
    (hX.2.2.1 i) (hY.2.2.1 i) hp (hc i) (z.prime_compat i)
  have hchart (i j : Fin t) := chart_compat_transport.{u, max v w} (f i) (f j) M N
    (piece (f i) (X.M i)) (piece (f i) (Y.M i))
    (piece (f j) (X.M j)) (piece (f j) (Y.M j))
    (hpieceX i) (hpieceY i) (hpieceX j) (hpieceY j)
    (X.alpha_overlap i j).toLinearMap (Y.alpha_overlap i j).toLinearMap
    (z.chart i) (z.chart j) (c i) (c j)
    (hX.2.2.2 i j) (hY.2.2.2 i j) (hc i) (hc j) (z.chart_compat i j)
  dsimp only
  intro m
  apply Prod.ext
  · funext i
    apply sub_eq_zero.mpr
    apply (compare_properties φ N (f i)).2.2.2.2.1
    rw [compare_eta]
    have h := LinearMap.congr_fun (hprime i)
      (LocalizedModule.mk (show restrict φ (extend φ M) from (1 : S) ⊗ₜ[R] m) 1)
    simp only [LinearMap.comp_apply, localMap, IsLocalizedModule.map_LocalizedModules] at h
    have hM : compare φ (f i) M
        (LocalizedModule.mk (show restrict φ (extend φ M) from (1 : S) ⊗ₜ[R] m) 1) =
        (1 : S) ⊗ₜ[R] LocalizedModule.mk m 1 := by
      have hd : (⟨(f i) ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers (f i)) = 1 :=
        Subtype.ext (pow_zero (f i))
      simpa only [hd] using (compare_properties φ M (f i)).2.1 m 1 0
    rw [hM] at h
    exact h
  · funext i j
    apply sub_eq_zero.mpr
    apply overlap_of_swap N (f i) (f j)
    have h := LinearMap.congr_fun (hchart i j)
      (LocalizedModule.mk (LocalizedModule.mk m 1) 1)
    simp only [LinearMap.comp_apply, localMap, IsLocalizedModule.map_LocalizedModules] at h
    have hM : swap (f i) (f j) M
        (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        LocalizedModule.mk (LocalizedModule.mk m 1) 1 :=
      (exists_swap (f i) (f j) M).exists.choose_spec m
    rw [hM, IsLocalizedModule.map_LocalizedModules] at h
    exact h

end FormalGlueing
