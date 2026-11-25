/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.FormalGlueingH0Localization
import WeilConjectures.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso

/-!
# An injective approximation to formal glueing data

Source: Stacks Project, More on Algebra, Proposition 05ER.
(blueprint: lem-weil-pbc-formal-glueing-injective-approximation).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

private theorem h0_equations {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {t : ℕ} (φ : R →+* S) (f : Fin t → R)
    (X : Data.{u, v, w} φ f) (h : h0 φ f X) :
    let : Algebra R S := φ.toAlgebra
    (∀ i, X.alpha i (LocalizedModule.mk h.val.1 1) =
      TensorProduct.tmul R (1 : S) (h.val.2 i)) ∧
    (∀ i j, X.alpha_overlap i j (LocalizedModule.mk (h.val.2 i) 1) =
      LocalizedModule.mk (h.val.2 j) 1) := by
  let : Algebra R S := φ.toAlgebra
  have hh := h.property
  change h.val ∈ _ ⊓ _ at hh
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply,
    LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe] at hh
  exact hh

private theorem localMap_mk {R : Type u} [CommRing R] (g : R)
    {M N : ModuleCat.{w} R} (h : M →ₗ[R] N) (m : M) (s : Submonoid.powers g) :
    localMap g h (LocalizedModule.mk m s) = LocalizedModule.mk (h m) s :=
  IsLocalizedModule.map_LocalizedModules _ h m s

private theorem restricted_localization {R : Type u} [CommRing R]
    (g : R) (M : ModuleCat.{w} R) :
    piece g (ModuleCat.of (Localization.Away g) (LocalizedModule.Away g M)) =
      localize g M := by
  dsimp [piece, restrict, ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj']
  congr 1
  ext r x
  exact IsScalarTower.algebraMap_smul (Localization.Away g) r x

private theorem transported_prime_compat {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (g : R)
    {P P' N : ModuleCat.{max u v w} S} {C C' D : ModuleCat.{max u v w} R}
    (hP : P = P') (hC : C = C')
    (α : localize g (restrict φ P) →ₗ[R] restrict φ (extend φ C))
    (α' : localize g (restrict φ P') →ₗ[R] restrict φ (extend φ C'))
    (hα : HEq α α') (β : localize g (restrict φ N) →ₗ[R] restrict φ (extend φ D))
    (p : P' →ₗ[S] N) (c : C' →ₗ[R] D)
    (hc : β.comp (localMap g (restrictMap φ p)) = (extendMapR φ c).comp α') :
    β.comp (localMap g (restrictMap φ (p.comp (eqToIso hP).hom.hom))) =
      (extendMapR φ (c.comp (eqToIso hC).hom.hom)).comp α := by
  subst P' C'
  have ha := eq_of_heq hα
  subst α'
  simpa using hc

private theorem transported_chart_compat {R : Type u} [CommRing R]
    (g k : R) {C C' D D' E F : ModuleCat.{w} R}
    (hC : C = C') (hD : D = D')
    (α : localize k C →ₗ[R] localize g D)
    (α' : localize k C' →ₗ[R] localize g D') (hα : HEq α α')
    (β : localize k E →ₗ[R] localize g F)
    (c : C' →ₗ[R] E) (d : D' →ₗ[R] F)
    (hc : β.comp (localMap k c) = (localMap g d).comp α') :
    β.comp (localMap k (c.comp (eqToIso hC).hom.hom)) =
      (localMap g (d.comp (eqToIso hD).hom.hom)).comp α := by
  subst C' D'
  have ha := eq_of_heq hα
  subst α'
  simpa using hc

/-- The projections of compatible sections extend to a glueing morphism, and its charts
are bijective. The prime component is specified on the unit pure tensors, after transport
along the given identification of the prime module.

Source: Stacks Project, More on Algebra, Proposition 05ER, second paragraph.
(blueprint: lem-weil-pbc-formal-glueing-injective-approximation).
Proof:
1. Set H to the submodule of compatible families defining h0. Its prime projection
   is R-linear. The tensor universal property extends it to the S-linear map
   s tensor h maps to s times h.val.1.
2. Each chart projection extends uniquely to H localized at f i, and is bijective
   by the h0 localization lemma. Transport these maps and the prime map along hobj.
3. The prime compatibility equation holds on (s tensor h)/1 by the defining
   prime/chart equation of h0 and the formula for compare. It holds everywhere by
   tensor induction and the localization universal property.
4. The overlap equation holds on (h/1)/1 by the defining overlap equation of h0
   and the formula for swap. Two applications of the localization universal
   property give the equation on all double fractions. The heterogeneous
   structural-map equalities in hobj transport these equations to Can.obj H.
5. Bundle the components with these two equations. The chart maps remain bijective
   under transport, and the prime formula at 1 tensor h follows from step 1.
The empty chart family gives just the tensor extension of the prime projection;
zero localizations cause no exception to the universal-property arguments. -/
private theorem exists_h0_morphism {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (hflat : φ.Flat) (X : Data.{u, v, max u v w} φ f) :
    letI : Algebra R S := φ.toAlgebra
    let H := ModuleCat.of R (h0 φ f X)
    let e := (eqToIso (hobj H).1).toLinearEquiv
    ∃ ψ : Can.obj H ⟶ X,
      (∀ i, Function.Bijective (ψ.chart i)) ∧
      ∀ h : h0 φ f X, ψ.prime (e.symm (TensorProduct.tmul R (1 : S) h)) = h.val.1 := by
  classical
  let : Algebra R S := φ.toAlgebra
  let H := ModuleCat.of R (h0 φ f X)
  let e := (eqToIso (hobj H).1).toLinearEquiv
  let : Module R X.M' := Module.compHom X.M' φ
  let : IsScalarTower R S X.M' := ⟨fun r s x ↦ by
    change (φ r * s) • x = φ r • (s • x)
    exact mul_smul _ _ _⟩
  let q : H →ₗ[R] X.M' :=
    (LinearMap.fst R _ _).comp (h0 φ f X).subtype
  let p : extend φ H →ₗ[S] X.M' :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton S (H →ₗ[R] X.M') q)
  have hp (s : S) (h : H) : p (TensorProduct.tmul R s h) = s • h.val.1 := rfl
  choose π hπ huniq hbij using exists_unique_bijective_h0_localization φ hflat f X
  let hC (i : Fin t) : piece (f i) ((Can.obj H).M i) = localize (f i) H :=
    (congrArg (piece (f i)) ((hobj H).2.1 i)).trans (restricted_localization (f i) H)
  let c (i : Fin t) := (π i).comp (eqToIso (hC i)).hom.hom
  have hc (i : Fin t) : Function.Bijective (c i) :=
    (hbij i).comp (eqToIso (hC i)).toLinearEquiv.bijective
  have hpc (i : Fin t) :
      (X.alpha i).toLinearMap.comp (localMap (f i) (restrictMap φ p)) =
        (extendMapR φ (π i)).comp (compare φ (f i) H) := by
    let T := Submonoid.powers (f i)
    let a := (X.alpha i).toLinearMap.comp
      (LocalizedModule.mkLinearMap T (restrict φ X.M'))
    let : IsLocalizedModule T a := IsLocalizedModule.of_linearEquiv T
      (LocalizedModule.mkLinearMap T (restrict φ X.M')) (X.alpha i)
    apply IsLocalizedModule.ext T
      (LocalizedModule.mkLinearMap T (restrict φ (extend φ H)))
      (IsLocalizedModule.map_units a)
    apply LinearMap.ext
    intro y
    change TensorProduct R S H at y
    induction y using TensorProduct.inductionOn with
    | tmul s h =>
      have hbase := LinearMap.congr_fun ((exists_compare φ (f i) H).exists.choose_spec)
        (TensorProduct.tmul R s h)
      change compare φ (f i) H (LocalizedModule.mk (TensorProduct.tmul R s h) 1) =
        TensorProduct.tmul R s (LocalizedModule.mk h 1) at hbase
      change X.alpha i
        (localMap (f i) (restrictMap φ p) (LocalizedModule.mk (TensorProduct.tmul R s h) 1)) =
        (extendMapR φ (π i))
          (compare φ (f i) H (LocalizedModule.mk (TensorProduct.tmul R s h) 1))
      rw [localMap_mk (M := restrict φ (extend φ H)) (N := restrict φ X.M')]
      change X.alpha i (LocalizedModule.mk (p (TensorProduct.tmul R s h)) 1) = _
      rw [hp]
      rw [(exists_localized_s_module φ (f i) X.M').choose_spec s h.val.1 1 |> Eq.symm]
      rw [X.alpha_smul, (h0_equations φ f X h).1 i]
      have hr := congrArg (extendMapR φ (π i)) hbase
      change (extendMapR φ (π i))
        (compare φ (f i) H (LocalizedModule.mk (TensorProduct.tmul R s h) 1)) =
        TensorProduct.tmul R s (π i (LocalizedModule.mk h 1)) at hr
      exact (show s • (TensorProduct.tmul R (1 : S) (h.val.2 i)) =
        TensorProduct.tmul R s (π i (LocalizedModule.mk h 1)) by
          rw [hπ i h]
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]).trans hr.symm
    | add y z hy hz => simpa only [map_add] using congrArg₂ (· + ·) hy hz
  have hcc (i j : Fin t) :
      (X.alpha_overlap i j).toLinearMap.comp (localMap (f j) (π i)) =
        (localMap (f i) (π j)).comp (swap (f i) (f j) H) := by
    let Ti := Submonoid.powers (f i)
    let Tj := Submonoid.powers (f j)
    let a := (X.alpha_overlap i j).toLinearMap.comp
      (LocalizedModule.mkLinearMap Tj (piece (f i) (X.M i)))
    let : IsLocalizedModule Tj a := IsLocalizedModule.of_linearEquiv Tj
      (LocalizedModule.mkLinearMap Tj (piece (f i) (X.M i))) (X.alpha_overlap i j)
    apply IsLocalizedModule.ext Tj
      (LocalizedModule.mkLinearMap Tj (localize (f i) H))
      (IsLocalizedModule.map_units a)
    apply IsLocalizedModule.ext Ti (LocalizedModule.mkLinearMap Ti H)
      (IsLocalizedModule.map_units
        (LocalizedModule.mkLinearMap Ti (piece (f j) (X.M j))))
    apply LinearMap.ext
    intro h
    change X.alpha_overlap i j
      (localMap (f j) (M := localize (f i) H) (N := piece (f i) (X.M i))
        (π i) (LocalizedModule.mk (S := Tj)
        (LocalizedModule.mk (S := Ti) h 1) 1)) =
      localMap (f i) (M := localize (f j) H) (N := piece (f j) (X.M j)) (π j)
        (swap (f i) (f j) H (LocalizedModule.mk (S := Tj)
          (LocalizedModule.mk (S := Ti) h 1) 1))
    rw [localMap_mk (M := localize (f i) H) (N := piece (f i) (X.M i))]
    rw [show swap (f i) (f j) H
      (LocalizedModule.mk (S := Tj) (LocalizedModule.mk (S := Ti) h 1) 1) =
      LocalizedModule.mk (S := Ti) (LocalizedModule.mk (S := Tj) h 1) 1 from
      (exists_swap (f i) (f j) H).exists.choose_spec h]
    rw [localMap_mk (M := localize (f j) H) (N := piece (f j) (X.M j))]
    rw [hπ i h, hπ j h]
    exact (h0_equations φ f X h).2 i j
  let ψ : Can.obj H ⟶ X :=
    { prime := p.comp e.toLinearMap
      chart := c
      prime_compat := fun i ↦ transported_prime_compat φ (f i)
        (hobj H).1 (hC i) ((Can.obj H).alpha i).toLinearMap
        (compare φ (f i) H) ((hobj H).2.2.1 i) (X.alpha i).toLinearMap p (π i) (hpc i)
      chart_compat := fun i j ↦ transported_chart_compat (f i) (f j)
        (hC i) (hC j) ((Can.obj H).alpha_overlap i j).toLinearMap
        (swap (f i) (f j) H) ((hobj H).2.2.2 i j)
        (X.alpha_overlap i j).toLinearMap (π i) (π j) (hcc i j) }
  refine ⟨ψ, hc, ?_⟩
  intro h
  change p (e (e.symm (TensorProduct.tmul R (1 : S) h))) = h.val.1
  rw [e.apply_symm_apply, hp, one_smul]


private theorem local_prime_bijective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {φ : R →+* S} {t : ℕ} {f : Fin t → R}
    {X Y : Data.{u, v, max u v w} φ f} (ψ : X ⟶ Y)
    (hc : ∀ i, Function.Bijective (ψ.chart i)) (i : Fin t) :
    Function.Bijective (localMap (f i) (restrictMap φ ψ.prime)) := by
  let : Algebra R S := φ.toAlgebra
  have hb : Function.Bijective (extendMapR φ (ψ.chart i)) := by
    exact ((LinearEquiv.ofBijective (ψ.chart i) (hc i)).baseChange R S).bijective
  have hcomp : Function.Bijective
      ((Y.alpha i).toLinearMap.comp (localMap (f i) (restrictMap φ ψ.prime))) := by
    rw [ψ.prime_compat i]
    exact hb.comp (X.alpha i).bijective
  constructor
  · intro x y h
    apply hcomp.1
    exact congrArg (Y.alpha i) h
  · intro y
    obtain ⟨x, hx⟩ := hcomp.2 (Y.alpha i y)
    exact ⟨x, (Y.alpha i).injective hx⟩

private theorem torsion_of_localizations_zero {R : Type u} [CommRing R]
    {P : Type w} [AddCommGroup P] [Module R P] (t : ℕ) (f : Fin t → R) (x : P)
    (hx : ∀ i, LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P x = 0) :
    x ∈ Ideal.primaryComponent P (Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  let J := (Submodule.span R ({x} : Set P)).annihilator
  have hIJ : I ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P)).mp (hx i)
    obtain ⟨n, hn⟩ := a.2
    change ∃ n : ℕ, (f i) ^ n ∈ J
    refine ⟨n, (Submodule.mem_annihilator_span_singleton x _).mpr ?_⟩
    simpa only [← hn, Submonoid.smul_def] using ha
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ
    (Submodule.fg_span (Set.finite_range f))
  apply (Ideal.primaryComponent_mem P I x).mpr
  refine ⟨n, (Submodule.mem_torsionBySet_iff (↑(I ^ n) : Set R) x).mpr ?_⟩
  intro a
  exact (Submodule.mem_annihilator_span_singleton x (a : R)).mp (hn a.2)

private theorem prime_kernel_torsion {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {φ : R →+* S} {t : ℕ} {f : Fin t → R}
    {X Y : Data.{u, v, max u v w} φ f} (ψ : X ⟶ Y)
    (hc : ∀ i, Function.Bijective (ψ.chart i)) (x : restrict φ X.M')
    (hx : ψ.prime x = 0) :
    x ∈ Ideal.primaryComponent (restrict φ X.M') (Ideal.span (Set.range f)) := by
  apply torsion_of_localizations_zero t f x
  intro i
  apply (local_prime_bijective ψ hc i).1
  simp [localMap, IsLocalizedModule.map_LocalizedModules, restrictMap, hx]

private theorem prime_cokernel_torsion {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {φ : R →+* S} {t : ℕ} {f : Fin t → R}
    {X Y : Data.{u, v, max u v w} φ f} (ψ : X ⟶ Y)
    (hc : ∀ i, Function.Bijective (ψ.chart i))
    (x : restrict φ (ModuleCat.of S (Y.M' ⧸ LinearMap.range ψ.prime))) :
    x ∈ Ideal.primaryComponent
      (restrict φ (ModuleCat.of S (Y.M' ⧸ LinearMap.range ψ.prime)))
      (Ideal.span (Set.range f)) := by
  apply torsion_of_localizations_zero t f x
  intro i
  let q := restrictMap φ (M := Y.M')
    (N := ModuleCat.of S (Y.M' ⧸ LinearMap.range ψ.prime))
    (LinearMap.range ψ.prime).mkQ
  have he : q.comp (restrictMap φ ψ.prime) = 0 := by
    ext y
    exact LinearMap.congr_fun (LinearMap.range_mkQ_comp ψ.prime) y
  have hl : (localMap (f i) q).comp (localMap (f i) (restrictMap φ ψ.prime)) = 0 := by
    rw [localMap, localMap, ← IsLocalizedModule.map_comp', he]
    exact map_zero _
  obtain ⟨y, rfl⟩ := (LinearMap.range ψ.prime).mkQ_surjective x
  obtain ⟨z, hz⟩ := (local_prime_bijective ψ hc i).2 (LocalizedModule.mk y 1)
  have h := LinearMap.congr_fun hl z
  rw [LinearMap.comp_apply, hz] at h
  simpa [localMap, IsLocalizedModule.map_LocalizedModules, q, restrictMap] using h

/-- Compatible sections give a morphism with bijective charts, injective prime map,
and ideal-power torsion prime cokernel.
Source: Stacks Project, More on Algebra, Proposition 05ER, second paragraph.
(blueprint: lem-weil-pbc-formal-glueing-injective-approximation).
Proof: take H to be the submodule of compatible families in the prime module times
all charts. Extend each chart projection across localization using the H0 localization
lemma. Extend the prime projection by the tensor universal property. The fraction
formulas for comparison and interchange show these maps satisfy the two morphism
relations: on a pure tensor fraction the prime relation is the defining prime/chart
relation of H, and on a double fraction the chart relation is its overlap relation.
The localized prime map is bijective because it is conjugate to the scalar extension
of the chart map. Localization exactness therefore makes its kernel and cokernel
vanish in every chart. For each element choose an annihilating power of each f i;
the sum of those exponents kills the element by the whole generated ideal power.
For a kernel element, torsion-submodule base change writes it as 1 tensor h for an
ideal-power torsion h in H. Its prime projection is zero. Its chart projections are
zero since torsion localizes to zero and the localized chart projections are
bijective. Thus h is zero as a compatible family, proving prime injectivity.
The construction is in universe max u v w, using a finite product and a submodule.
If t is zero, H is the prime module and the same torsion comparison proves the
prime map injective; the empty chart conclusions are vacuous. If the ideal is the
unit ideal, the asserted torsion cokernel is zero. -/
theorem exists_injective_approximation {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (hflat : φ.Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (X : Data.{u, v, max u v w} φ f) :
    ∃ (H : ModuleCat.{max u v w} R) (ψ : Can.obj H ⟶ X),
      Function.Injective ψ.prime ∧ (∀ i, Function.Bijective (ψ.chart i)) ∧
      ∀ x : restrict φ (ModuleCat.of S (X.M' ⧸ LinearMap.range ψ.prime)),
        ∃ n : ℕ, 1 ≤ n ∧ ∀ r ∈ (Ideal.span (Set.range f)) ^ n, r • x = 0 := by
  classical
  let : Algebra R S := φ.toAlgebra
  let H := ModuleCat.of R (h0 φ f X)
  let e := (eqToIso (hobj H).1).toLinearEquiv
  obtain ⟨ψ, hc, hp⟩ := exists_h0_morphism φ t f Can hobj hflat X
  refine ⟨H, ψ, ?_, hc, ?_⟩
  · apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro y hy
    change ψ.prime y = 0 at hy
    have ht := prime_kernel_torsion ψ hc y hy
    have ht' : e y ∈ Ideal.primaryComponent (TensorProduct R S H)
        (Ideal.span (Set.range f)) := by
      obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (restrict φ (Can.obj H).M') _ y).mp ht
      apply (Ideal.primaryComponent_mem _ _ (e y)).mpr
      refine ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr ?_⟩
      intro a
      rw [← algebraMap_smul S (a : R), ← e.map_smul]
      have hkill := (Submodule.mem_torsionBySet_iff
        (↑(Ideal.span (Set.range f) ^ n) : Set R)
        (show restrict φ (Can.obj H).M' from y)).mp hn a
      change φ (a : R) • y = 0 at hkill
      simpa only [RingHom.algebraMap_toAlgebra, map_zero] using congrArg e hkill
    obtain ⟨h, hh⟩ := (Ideal.primaryComponent_baseChange_bijective
      (Ideal.span (Set.range f)) (Submodule.fg_span (Set.finite_range f))
      hflat hquot H).2 ⟨e y, ht'⟩
    have hh' : TensorProduct.tmul R (1 : S) (h : H) = e y := congrArg Subtype.val hh
    have hprime : (h : H).val.1 = 0 := by
      rw [← hp (h : H)]
      change ψ.prime (e.symm (TensorProduct.tmul R (1 : S) (h : H))) = 0
      rw [hh', e.symm_apply_apply]
      exact hy
    have hchart : ∀ i, (h : H).val.2 i = 0 := by
      intro i
      obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem H _ (h : H)).mp h.property
      have hkill : (f i) ^ n • (h : H) = 0 :=
        (Submodule.mem_torsionBySet_iff _ _).mp hn
          ⟨(f i) ^ n, Ideal.pow_mem_pow (show f i ∈ Ideal.span (Set.range f) from
            Ideal.subset_span ⟨i, rfl⟩) n⟩
      have hz := congrArg (fun z : H ↦ z.val.2 i) hkill
      have hu : IsUnit (algebraMap R (Localization.Away (f i)) ((f i) ^ n)) :=
        IsLocalization.map_units (Localization.Away (f i))
          (⟨(f i) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (f i))
      exact hu.smul_eq_zero.mp hz
    have hzero : (h : H) = 0 := by
      apply Subtype.ext
      exact Prod.ext hprime (funext hchart)
    have hey : e y = 0 := by rw [← hh', hzero, TensorProduct.tmul_zero]
    have hyzero : y = 0 := e.injective (hey.trans e.map_zero.symm)
    exact hyzero
  · intro x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem _ _ x).mp
      (prime_cokernel_torsion ψ hc x)
    refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
    intro r hr
    exact (Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨r, Ideal.pow_le_pow_right (Nat.le_succ n) hr⟩

end FormalGlueing
