/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.FormalGlueingMorphismTuple
import WeilConjectures.RingTheory.FormalGlueingComplexExact

/-!
# Lifting morphisms of canonical formal glueing data

Source: Stacks Project, More on Algebra, Lemmas 05EK and 05EM.
(blueprint: lem-weil-pbc-formal-glueing-morphism-lifting).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

private theorem transport_prime {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S)
    (M N : ModuleCat.{max u v w} R) (A B : ModuleCat.{max u v w} S)
    (ha : A = extend φ M) (hb : B = extend φ N) (p : A →ₗ[S] B) :
    ∃ q : extend φ M →ₗ[S] extend φ N, HEq p q := by
  subst A
  subst B
  exact ⟨p, HEq.rfl⟩

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

private theorem transport_chart {R : Type u} [CommRing R] (a : R)
    (M N : ModuleCat.{w} R)
    (A B : ModuleCat.{max u w} (Localization.Away a))
    (ha : A = ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M))
    (hb : B = ModuleCat.of (Localization.Away a) (LocalizedModule.Away a N))
    (c : piece a A →ₗ[R] piece a B) :
    ∃ d : localize a M →ₗ[R] localize a N, HEq c d := by
  subst A
  subst B
  have hm := canonical_piece_eq a M
  have hn := canonical_piece_eq a N
  generalize piece a (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) = A
    at c hm
  generalize piece a (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a N)) = B
    at c hn
  subst A
  subst B
  exact ⟨c, HEq.rfl⟩

private theorem components_ext {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {φ : R →+* S} {t : ℕ} {f : Fin t → R}
    {X Y : Data.{u, v, max u v w} φ f} {z z' : X ⟶ Y}
    (hp : z.prime = z'.prime) (hc : ∀ i, z.chart i = z'.chart i) : z = z' := by
  cases z
  cases z'
  cases hp
  cases funext hc
  rfl

/-- Every morphism between canonical objects lifts to a linear map.
Source: Stacks, More on Algebra, Lemmas 05EK and 05EM; steps 3–4 and 6 of
Proposition 05ER's formal-glueing equivalence proof.
(blueprint: lem-weil-pbc-formal-glueing-morphism-lifting).
Proof: for a morphism z and m in M, form the tuple (z.prime (1 tensor m),
(z.chart i (m/1))_i). The prime compatibility equation says its first compatibility
difference is zero under the canonical comparison. The chart compatibility equation
says the two chart values agree in the iterated localization. Clearing both denominators
shows they agree in the product localization, so every overlap difference is zero.
Exactness of the formal glueing complex produces a preimage in N; its injective initial
map makes that preimage unique. Define u(m) by this unique preimage. Injectivity applied
to the images of sums and scalar multiples proves that u is linear. On pure tensors,
u extended to S agrees with z.prime. On m/1 each localized u agrees with z.chart i;
uniqueness for localization extends this to every fraction. Thus Can.map u = z by
componentwise equality. Empty chart families are covered by the same exact complex;
zero charts and zero modules do not require cancellation in R. -/
theorem canonical_map_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (hmap : (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (Can.map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((Can.map h).chart i) (localMap (f i) h.hom)))
    (hflat : φ.Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (M N : ModuleCat.{max u v w} R) :
    Function.Surjective (Can.map : (M ⟶ N) → (Can.obj M ⟶ Can.obj N)) := by
  classical
  let : Algebra R S := φ.toAlgebra
  intro z
  obtain ⟨p, hp⟩ := transport_prime φ M N (Can.obj M).M' (Can.obj N).M'
    (hobj M).1 (hobj N).1 z.prime
  have charts (i : Fin t) := transport_chart (f i) M N ((Can.obj M).M i)
    ((Can.obj N).M i) ((hobj M).2.1 i) ((hobj N).2.1 i) (z.chart i)
  choose c hc using charts
  obtain ⟨hinj, hexact⟩ := RingTheory.formalGlueingComplexExact φ hflat t f hquot N
  have recover (m : M) : ∃! n : N,
      TensorProduct.tmul R (1 : S) n = p (TensorProduct.tmul R (1 : S) m) ∧
        ∀ i, LocalizedModule.mk n 1 = c i (LocalizedModule.mk m 1) := by
    have hk := canonical_tuple_compatible φ t f M N (Can.obj M) (Can.obj N)
      (hobj M) (hobj N) z p c hp hc m
    obtain ⟨n, hn⟩ := (hexact _).mp hk
    refine ⟨n, ⟨congrArg Prod.fst hn, fun i ↦ congrArg (fun q ↦ q.2 i) hn⟩, ?_⟩
    intro n' hn'
    apply hinj
    apply Prod.ext
    · exact hn'.1.trans (congrArg Prod.fst hn).symm
    · funext i
      exact (hn'.2 i).trans (congrArg (fun q ↦ q.2 i) hn).symm
  let value (m : M) : N := (recover m).exists.choose
  have hv (m : M) :
      TensorProduct.tmul R (1 : S) (value m) = p (TensorProduct.tmul R (1 : S) m) ∧
        ∀ i, LocalizedModule.mk (value m) 1 = c i (LocalizedModule.mk m 1) :=
    (recover m).exists.choose_spec
  have unique (m : M) (n : N)
      (hn : TensorProduct.tmul R (1 : S) n = p (TensorProduct.tmul R (1 : S) m) ∧
        ∀ i, LocalizedModule.mk n 1 = c i (LocalizedModule.mk m 1)) :
      n = value m := (recover m).unique hn (hv m)
  let h : M →ₗ[R] N :=
    { toFun := value
      map_add' := by
        intro x y
        apply (unique (x + y) (value x + value y) ?_).symm
        constructor
        · simp only [TensorProduct.tmul_add, map_add, (hv x).1, (hv y).1]
        · intro i
          simpa only [← LocalizedModule.mkLinearMap_apply, map_add] using
            congrArg₂ (· + ·) ((hv x).2 i) ((hv y).2 i)
      map_smul' := by
        intro r x
        apply (unique (r • x) (r • value x) ?_).symm
        constructor
        · rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, (hv x).1]
          exact (p.map_smul (algebraMap R S r) _).symm
        · intro i
          simpa only [← LocalizedModule.mkLinearMap_apply, map_smul] using
            congrArg (fun n ↦ r • n) ((hv x).2 i) }
  have hext : extendMap φ h = p := by
    apply LinearMap.ext
    intro x
    change TensorProduct R S M at x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
      change TensorProduct.tmul R s (h m) = p (TensorProduct.tmul R s m)
      rw [show TensorProduct.tmul R s (h m) = s • (TensorProduct.tmul R (1 : S) (value m)) by
        simp [h, TensorProduct.smul_tmul']]
      rw [(hv m).1]
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (p.map_smul s (TensorProduct.tmul R (1 : S) m)).symm
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hloc (i : Fin t) : localMap (f i) h = c i := by
    apply IsLocalizedModule.ext (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap _ M)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap _ N))
    ext m
    simpa only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply,
      localMap, IsLocalizedModule.map_LocalizedModules, h, LinearMap.coe_mk,
      AddHom.coe_mk] using (hv m).2 i
  refine ⟨ModuleCat.ofHom h, ?_⟩
  apply components_ext
  · exact eq_of_heq ((hmap M N (ModuleCat.ofHom h)).1.trans
      ((heq_of_eq hext).trans hp.symm))
  · intro i
    exact eq_of_heq (((hmap M N (ModuleCat.ofHom h)).2 i).trans
      ((heq_of_eq (hloc i)).trans (hc i).symm))

end FormalGlueing
