/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
import WeilConjectures.AlgebraicGeometry.FormalGlueingCanonicalMaps

/-!
# Canonical morphisms between prescribed formal glueing objects

Source: Stacks Project, More on Algebra, Remark 05EL.
(blueprint: lem-weil-pbc-formal-glueing-canonical-functor-maps).
-/

@[expose] public section

universe u v w

open CategoryTheory
namespace FormalGlueing

private theorem canonical_piece {R : Type u} [CommRing R]
    (a : R) (M : ModuleCat.{w} R) :
    piece a (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) =
      localize a M := by
  apply congrArg (fun inst : Module R (LocalizedModule.Away a M) ↦
    @ModuleCat.of R _ (LocalizedModule.Away a M) _ inst)
  apply Module.ext'
  intro r x
  exact algebraMap_smul (Localization.Away a) r x

private theorem swap_natural {R : Type u} [CommRing R]
    {M N : ModuleCat.{w} R} (a b : R) (h : M →ₗ[R] N) :
    (swap a b N).comp (localMap b (localMap a h)) =
      (localMap a (localMap b h)).comp (swap a b M) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | _ m t =>
    induction m using LocalizedModule.induction_on with
    | _ p s =>
      rcases s with ⟨_, n, rfl⟩
      rcases t with ⟨_, k, rfl⟩
      simp only [LinearMap.comp_apply, localMap, IsLocalizedModule.map_LocalizedModules,
        (swap_properties M a b).2.2.1, (swap_properties N a b).2.2.1]

private theorem compare_natural {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : ModuleCat.{w} R} (a : R) (h : M →ₗ[R] N) :
    (compare φ a N).comp (localMap a (restrictMap φ (extendMap φ h))) =
      (extendMapR φ (localMap a h)).comp (compare φ a M) := by
  let : Algebra R S := φ.toAlgebra
  have hu : ∀ t : Submonoid.powers a,
      IsUnit (algebraMap R (Module.End R (restrict φ (extend φ (localize a N)))) t) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).mpr (compare_properties φ N a).1).pow n
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap _ (restrict φ (extend φ M))) hu
  ext x
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply,
    localMap, IsLocalizedModule.map_LocalizedModules]
  rw [show compare φ a N (LocalizedModule.mk (restrictMap φ (extendMap φ h) x) 1) =
      restrictMap φ (extendMap φ (LocalizedModule.mkLinearMap _ N))
        (restrictMap φ (extendMap φ h) x) from
      LinearMap.congr_fun (exists_compare φ a N).exists.choose_spec _,
    show compare φ a M (LocalizedModule.mk x 1) =
      restrictMap φ (extendMap φ (LocalizedModule.mkLinearMap _ M)) x from
      LinearMap.congr_fun (exists_compare φ a M).exists.choose_spec x]
  change TensorProduct R S M at x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    simp [extendMap, extendMapR, restrictMap, IsLocalizedModule.map_LocalizedModules]
  | add x y hx hy => simp [hx, hy]

private def castMap {A : Type u} [CommRing A]
    {X X' Y Y' : ModuleCat.{w} A} (hx : X = X') (hy : Y = Y')
    (h : X' →ₗ[A] Y') : X →ₗ[A] Y := by
  subst X
  subst Y
  exact h

private theorem castMap_heq {A : Type u} [CommRing A]
    {X X' Y Y' : ModuleCat.{w} A} (hx : X = X') (hy : Y = Y')
    (h : X' →ₗ[A] Y') : HEq (castMap hx hy h) h := by
  subst X
  subst Y
  rfl

private theorem cast_compare_compat {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (a : R)
    {M N : ModuleCat.{max u v w} R} (h : M →ₗ[R] N)
    {XP YP : ModuleCat.{max u v w} S} {XC YC : ModuleCat.{max u v w} R}
    (hXP : XP = extend φ M) (hYP : YP = extend φ N)
    (hXC : XC = localize a M) (hYC : YC = localize a N)
    (α : localize a (restrict φ XP) →ₗ[R] restrict φ (extend φ XC))
    (β : localize a (restrict φ YP) →ₗ[R] restrict φ (extend φ YC))
    (hα : HEq α (compare φ a M)) (hβ : HEq β (compare φ a N)) :
    β.comp (localMap a (restrictMap φ (castMap hXP hYP (extendMap φ h)))) =
      (extendMapR φ (castMap hXC hYC (localMap a h))).comp α := by
  subst XP
  subst YP
  subst XC
  subst YC
  cases eq_of_heq hα
  cases eq_of_heq hβ
  exact compare_natural φ a h

private theorem cast_swap_compat {R : Type u} [CommRing R] (a b : R)
    {M N : ModuleCat.{w} R} (h : M →ₗ[R] N)
    {XA YA XB YB : ModuleCat.{max u w} R}
    (hXA : XA = localize a M) (hYA : YA = localize a N)
    (hXB : XB = localize b M) (hYB : YB = localize b N)
    (α : localize b XA →ₗ[R] localize a XB)
    (β : localize b YA →ₗ[R] localize a YB)
    (hα : HEq α (swap a b M)) (hβ : HEq β (swap a b N)) :
    β.comp (localMap b (castMap hXA hYA (localMap a h))) =
      (localMap a (castMap hXB hYB (localMap b h))).comp α := by
  subst XA
  subst YA
  subst XB
  subst YB
  cases eq_of_heq hα
  cases eq_of_heq hβ
  exact swap_natural a b h

private theorem castMap_id {A : Type u} [CommRing A]
    {X X' : ModuleCat.{w} A} (hx : X = X') :
    castMap hx hx LinearMap.id = LinearMap.id := by
  subst X
  rfl

private theorem castMap_comp {A : Type u} [CommRing A]
    {X X' Y Y' Z Z' : ModuleCat.{w} A} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    (h : X' →ₗ[A] Y') (k : Y' →ₗ[A] Z') :
    castMap hx hz (k.comp h) = (castMap hy hz k).comp (castMap hx hy h) := by
  subst X
  subst Y
  subst Z
  rfl

private theorem hom_ext {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {φ : R →+* S} {t : ℕ} {f : Fin t → R} {X Y : Data.{u, v, w} φ f}
    {h k : X ⟶ Y} (hp : h.prime = k.prime) (hc : ∀ i, h.chart i = k.chart i) :
    h = k := by
  cases h
  cases k
  dsimp only at hp hc
  cases hp
  cases funext hc
  rfl

private theorem extend_id {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{w} R) :
    extendMap φ (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  let : Algebra R S := φ.toAlgebra
  exact LinearMap.baseChange_id

private theorem extend_comp {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) {M N P : ModuleCat.{w} R} (h : M →ₗ[R] N) (k : N →ₗ[R] P) :
    extendMap φ (k.comp h) = (extendMap φ k).comp (extendMap φ h) := by
  let : Algebra R S := φ.toAlgebra
  exact LinearMap.baseChange_comp _ _

/-- Given canonical glueing objects, construct their canonical morphism assignment.
This constructs maps; it does not identify maps of an arbitrary functor.
Source: Stacks Project, More on Algebra, Remark 05EL, construction of `Can` on maps.
(blueprint: lem-weil-pbc-formal-glueing-canonical-functor-maps).
Proof: transport extendMap φ h.hom and localMap (f i) h.hom along the given
prime and chart module equalities. For charts, restriction to R agrees with the
localized R-action by algebraMap_smul. For prime compatibility, compare_properties
shows that powers of f_i act
invertibly on the target. Localization extensionality reduces the equation to
fractions with denominator one. The defining equation of exists_compare then
reduces it to naturality of tensoring the localization map, proved by tensor
induction and the fraction formula for localization maps. The chart compatibility equation sends
(m/f_i^a)/f_j^b to (h(m)/f_j^b)/f_i^a on both sides, by swap_properties.
These equations construct a Hom for every h. Tensor base change and localization
preserve identities and composition (LinearMap.baseChange_id,
LinearMap.baseChange_comp, IsLocalizedModule.map_id and map_comp'). Hence the
constructed Homs preserve them componentwise. Hom has only prime and chart data;
its other fields are proofs, so componentwise equality proves both laws.
Transport along the fixed object equalities respects these laws. Empty chart
families and zero localizations cause no exception to these calculations. -/
theorem canonical_functor_maps {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (obj : ModuleCat.{max u v w} R → Data.{u, v, max u v w} φ f)
    (hobj : ∀ M : ModuleCat.{max u v w} R,
      (obj M).M' = extend φ M ∧
      (∀ i : Fin t, (obj M).M i =
        ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
      (∀ i : Fin t, HEq ((obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
      (∀ i j : Fin t,
        HEq ((obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))) :
    ∃ map : ∀ {M N : ModuleCat.{max u v w} R}, (M ⟶ N) → (obj M ⟶ obj N),
      (∀ M, map (𝟙 M) = 𝟙 (obj M)) ∧
      (∀ {M N P} (h : M ⟶ N) (k : N ⟶ P), map (h ≫ k) = map h ≫ map k) ∧
      (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((map h).chart i) (localMap (f i) h.hom)) := by
  let hp (M : ModuleCat.{max u v w} R) := (hobj M).1
  let hc (M : ModuleCat.{max u v w} R) (i : Fin t) :
      piece (f i) ((obj M).M i) = localize (f i) M :=
    (congrArg (piece (f i)) ((hobj M).2.1 i)).trans (canonical_piece (f i) M)
  let map {M N : ModuleCat.{max u v w} R} (h : M ⟶ N) : obj M ⟶ obj N :=
    { prime := castMap (hp M) (hp N) (extendMap φ h.hom)
      chart := fun i ↦ castMap (hc M i) (hc N i) (localMap (f i) h.hom)
      prime_compat := fun i ↦ cast_compare_compat φ (f i) h.hom
        (hp M) (hp N) (hc M i) (hc N i)
        ((obj M).alpha i).toLinearMap ((obj N).alpha i).toLinearMap
        ((hobj M).2.2.1 i) ((hobj N).2.2.1 i)
      chart_compat := fun i j ↦ cast_swap_compat (f i) (f j) h.hom
        (hc M i) (hc N i) (hc M j) (hc N j)
        ((obj M).alpha_overlap i j).toLinearMap
        ((obj N).alpha_overlap i j).toLinearMap
        ((hobj M).2.2.2 i j) ((hobj N).2.2.2 i j) }
  refine ⟨@map, ?_, ?_, ?_⟩
  · intro M
    apply hom_ext
    · change castMap (hp M) (hp M) (extendMap φ LinearMap.id) = LinearMap.id
      rw [extend_id, castMap_id]
    · intro i
      change castMap (hc M i) (hc M i) (localMap (f i) LinearMap.id) = LinearMap.id
      rw [show localMap (f i) (LinearMap.id : M →ₗ[R] M) = LinearMap.id from
        IsLocalizedModule.map_id _ _, castMap_id]
  · intro M N P h k
    apply hom_ext
    · change castMap (hp M) (hp P) (extendMap φ (k.hom.comp h.hom)) =
        (castMap (hp N) (hp P) (extendMap φ k.hom)).comp
          (castMap (hp M) (hp N) (extendMap φ h.hom))
      rw [extend_comp, castMap_comp]
    · intro i
      change castMap (hc M i) (hc P i) (localMap (f i) (k.hom.comp h.hom)) =
        (castMap (hc N i) (hc P i) (localMap (f i) k.hom)).comp
          (castMap (hc M i) (hc N i) (localMap (f i) h.hom))
      rw [show localMap (f i) (k.hom.comp h.hom) =
        (localMap (f i) k.hom).comp (localMap (f i) h.hom) from
        IsLocalizedModule.map_comp' _ _ _ _ _ _, castMap_comp]
  · intro M N h
    exact ⟨castMap_heq (hp M) (hp N) _, fun i ↦ castMap_heq (hc M i) (hc N i) _⟩

end FormalGlueing
