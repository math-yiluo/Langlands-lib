/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Clearing denominators in Tor classes

(blueprint: lem-pc-tor-localization-denominators)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ModuleCat

private theorem tensor_coefficient_fractions
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) [Algebra B C] (S : Submonoid B) [IsLocalization S C]
    (M : ModuleCat.{u} A)
    (f : (restrictScalars φ).obj (of B B) ⟶
      (restrictScalars ((algebraMap B C).comp φ)).obj (of C C))
    (hf : ∀ b : B, f b = algebraMap B C b) :
    (∀ x : ↑(M ⊗ (restrictScalars ((algebraMap B C).comp φ)).obj (of C C) : ModuleCat A),
      ∃ s : S, ∃ y : ↑(M ⊗ (restrictScalars φ).obj (of B B) : ModuleCat A),
        (𝟙 M ⊗ₘ (restrictScalars ((algebraMap B C).comp φ)).map
          (ofHom (LinearMap.mulLeft C (algebraMap B C s)))) x = (𝟙 M ⊗ₘ f) y) ∧
    (∀ y : ↑(M ⊗ (restrictScalars φ).obj (of B B) : ModuleCat A), (𝟙 M ⊗ₘ f) y = 0 →
      ∃ s : S, (𝟙 M ⊗ₘ (restrictScalars φ).map
        (ofHom (LinearMap.mulLeft B (s : B)))) y = 0) := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let g := TensorProduct.AlgebraTensorModule.rTensor A M (Algebra.linearMap B C)
  have hg : IsLocalizedModule S g := inferInstance
  have hmap (y : ↑(M ⊗ (restrictScalars φ).obj (of B B) : ModuleCat A)) :
      (TensorProduct.comm A M C) ((𝟙 M ⊗ₘ f) y) =
        g ((TensorProduct.comm A M B) y) := by
    induction y using TensorProduct.inductionOn with
    | tmul m b => simp [g, hf]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmulC (s : B)
      (x : ↑(M ⊗ (restrictScalars ((algebraMap B C).comp φ)).obj (of C C) : ModuleCat A)) :
      (TensorProduct.comm A M C)
        ((𝟙 M ⊗ₘ (restrictScalars ((algebraMap B C).comp φ)).map
          (ofHom (LinearMap.mulLeft C (algebraMap B C s)))) x) =
        s • (TensorProduct.comm A M C) x := by
    induction x using TensorProduct.inductionOn with
    | tmul m c => simp [TensorProduct.smul_tmul', Algebra.smul_def]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hmulB (s : B) (y : ↑(M ⊗ (restrictScalars φ).obj (of B B) : ModuleCat A)) :
      (TensorProduct.comm A M B)
        ((𝟙 M ⊗ₘ (restrictScalars φ).map (ofHom (LinearMap.mulLeft B (s : B)))) y) =
        s • (TensorProduct.comm A M B) y := by
    induction y using TensorProduct.inductionOn with
    | tmul m b => simp [TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  constructor
  · intro x
    obtain ⟨⟨z, s⟩, hs⟩ := IsLocalizedModule.surj S g ((TensorProduct.comm A M C) x)
    refine ⟨s, (TensorProduct.comm A M B).symm z, ?_⟩
    apply (TensorProduct.comm A M C).injective
    rw [hmulC, hmap, LinearEquiv.apply_symm_apply]
    exact hs
  · intro y hy
    have hz : g ((TensorProduct.comm A M B) y) = g 0 := by rw [← hmap, hy]; simp
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := g) hz
    refine ⟨s, ?_⟩
    apply (TensorProduct.comm A M B).injective
    rw [hmulB, map_zero]
    simpa only [Submonoid.smul_def, smul_zero] using hs

/-- Clearing denominators commutes with passing to homology of an arbitrary tensor complex.

Source: Stacks Project, Tag 0B67, `lemma-tor-amplitude-localization`, the localized
homology identity in the proof; the cycle argument does not require a resolution.
Proof: regard Q tensor_A B as a B-complex. Tensor associativity identifies
Q tensor_A C with its S-localization, and the displayed map with its localization
map. Represent x by a cycle in degree j. Clear its denominator to obtain z over B.
The differential of z maps to zero. The localization equality criterion supplies
a second denominator annihilating this differential. Multiply z by that denominator:
it is now a cycle, whose homology class is y. The product s of the two denominators
belongs to S; its image in C is a unit u. Multiplication by u on the localized cycle
is the image of the cycle defining y. Passing to homology gives the equation below.
The coefficient multiplication map induces precisely this action on the complex.
For j = 0 the outgoing differential is zero and the second denominator may be one.
For Q = 0 both classes are zero; if zero belongs to S the localized complex is zero.
(blueprint: lem-pc-tor-localization-denominators)
-/
private theorem tensor_complex_localization_denominators
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) [Algebra B C] (S : Submonoid B) [IsLocalization S C]
    (Q : ChainComplex (ModuleCat.{u} A) ℕ) (j : ℕ)
    (f : (restrictScalars φ).obj (of B B) ⟶
      (restrictScalars ((algebraMap B C).comp φ)).obj (of C C))
    (hf : ∀ b : B, f b = algebraMap B C b)
    (x : (((tensorRight
      ((restrictScalars ((algebraMap B C).comp φ)).obj (of C C))).mapHomologicalComplex
        (.down ℕ)).obj Q).homology j) :
    ∃ u : Cˣ, ∃ y : (((tensorRight ((restrictScalars φ).obj (of B B))).mapHomologicalComplex
        (.down ℕ)).obj Q).homology j,
      (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat A)).map
            ((restrictScalars ((algebraMap B C).comp φ)).map
              (u.mulLeftLinearEquiv C C).toModuleIso.hom)) (.down ℕ)).app Q) j) x =
        (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex
            ((tensoringRight (ModuleCat A)).map f) (.down ℕ)).app Q) j) y := by
  classical
  let : Algebra A B := φ.toAlgebra
  let : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  let MB := (restrictScalars φ).obj (of B B)
  let MC := (restrictScalars ((algebraMap B C).comp φ)).obj (of C C)
  let K := ((tensorRight MB).mapHomologicalComplex (.down ℕ)).obj Q
  let L := ((tensorRight MC).mapHomologicalComplex (.down ℕ)).obj Q
  let mb (r : B) : MB ⟶ MB := (restrictScalars φ).map (ofHom (LinearMap.mulLeft B r))
  let mc (r : C) : MC ⟶ MC := (restrictScalars ((algebraMap B C).comp φ)).map
    (ofHom (LinearMap.mulLeft C r))
  let b (r : B) : K ⟶ K := (NatTrans.mapHomologicalComplex
    ((tensoringRight (ModuleCat A)).map (mb r)) (.down ℕ)).app Q
  let c (r : C) : L ⟶ L := (NatTrans.mapHomologicalComplex
    ((tensoringRight (ModuleCat A)).map (mc r)) (.down ℕ)).app Q
  let t : K ⟶ L := (NatTrans.mapHomologicalComplex
    ((tensoringRight (ModuleCat A)).map f) (.down ℕ)).app Q
  have bc (r : B) : b r ≫ t = t ≫ c (algebraMap B C r) := by
    ext i : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext m z
    change B at z
    change m ⊗ₜ[A] f (r * z) =
      m ⊗ₜ[A] ((algebraMap B C r) * (show C from f z) : C)
    rw [hf, hf, map_mul]
  have cc (r s : C) : c r ≫ c s = c (s * r) := by
    ext i : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext m z
    change C at z
    change m ⊗ₜ[A] (s * (r * z)) = m ⊗ₜ[A] ((s * r) * z)
    rw [mul_assoc]
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ j)).mp inferInstance x
  obtain ⟨s, z, hs⟩ := (tensor_coefficient_fractions A B C φ S (Q.X j) f hf).1
    ((L.iCycles j) v)
  change (c (algebraMap B C s)).f j ((L.iCycles j) v) = t.f j z at hs
  let k := (ComplexShape.down ℕ).next j
  have hd : L.d j k ((L.iCycles j) v) = 0 := by
    change ((L.iCycles j) ≫ L.d j k) v = 0
    rw [L.iCycles_d]
    rfl
  have hdz : t.f k (K.d j k z) = 0 := by
    have ht := congrArg (fun q ↦ q z) (t.comm j k)
    have hc := congrArg (fun q ↦ q ((L.iCycles j) v))
      ((c (algebraMap B C s)).comm j k)
    simp only [ModuleCat.comp_apply] at ht hc
    rw [← ht, ← hs, hc, hd]
    exact map_zero _
  obtain ⟨s', hs'⟩ := (tensor_coefficient_fractions A B C φ S (Q.X k) f hf).2
    (K.d j k z) hdz
  change (b (s' : B)).f k (K.d j k z) = 0 at hs'
  have hcycle : (K.sc j).g ((b (s' : B)).f j z) = 0 := by
    have hb := congrArg (fun q ↦ q z) ((b (s' : B)).comm j k)
    simp only [ModuleCat.comp_apply] at hb
    change K.d j k ((b (s' : B)).f j z) = 0
    exact hb.trans hs'
  let w := (K.sc j).cyclesMk ((b (s' : B)).f j z) hcycle
  have hw : (K.iCycles j) w = (b (s' : B)).f j z := by
    exact (K.sc j).i_cyclesMk _ _
  obtain ⟨u, hu⟩ := IsLocalization.map_units C (s' * s)
  refine ⟨u, (K.homologyπ j) w, ?_⟩
  change (HomologicalComplex.homologyMap (c (u : C)) j) x =
    (HomologicalComplex.homologyMap t j) ((K.homologyπ j) w)
  rw [← hv]
  have hcπ := congrArg (fun q ↦ q v) (HomologicalComplex.homologyπ_naturality (c (u : C)) j)
  have htπ := congrArg (fun q ↦ q w) (HomologicalComplex.homologyπ_naturality t j)
  simp only [ModuleCat.comp_apply] at hcπ htπ
  rw [hcπ, htπ]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles j)).mp inferInstance
  have hci := congrArg (fun q ↦ q v) (HomologicalComplex.cyclesMap_i (c (u : C)) j)
  have hti := congrArg (fun q ↦ q w) (HomologicalComplex.cyclesMap_i t j)
  simp only [ModuleCat.comp_apply] at hci hti
  rw [hci, hti, hw]
  have hbc := congrArg (fun q ↦ q.f j z) (bc (s' : B))
  have hcc := congrArg (fun q ↦ q.f j ((L.iCycles j) v))
    (cc (algebraMap B C s) (algebraMap B C s'))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hbc hcc
  rw [hbc, ← hs, hcc]
  rw [show (u : C) = algebraMap B C s' * algebraMap B C s from by
    simpa only [Submonoid.coe_mul, map_mul] using hu]

/-- Every localized Tor class has a unit multiple in the image of the coefficient map.
The multiplier is induced by multiplication on the coefficient algebra, rather than
an arbitrary action on Tor. The map `f` is specified on elements, so it is exactly
restriction of the localization map with the displayed scalar structures.

Source: Stacks Project, Tag 0B67, the localized derived-tensor homology identity in
its proof, specialized to B in degree zero; expanded here to individual classes.
Proof: choose a free A-resolution Q of N. Balancedness identifies the two Tor'
objects, naturally in the coefficient, with H_j(B tensor_A Q) and H_j(C tensor_A Q).
Tensor associativity identifies the latter complex with the localization at S of
the former B-complex. Localization is exact, hence its homology is the localization
of H_j(B tensor_A Q). More explicitly, represent a localized homology class by a
cycle. Clear its denominator to obtain a chain over B. Its differential becomes
zero after localization, so a second denominator annihilates that differential.
Multiplying by this second denominator gives a cycle over B. The product s of the
two denominators belongs to S, and its image in C is a unit u. The original class
multiplied by u is the image of the class y of this cycle. Naturality of balancedness
identifies multiplication by u with the displayed Tor' map, and the coefficient
map with Tor'(f,N). This also works in degree zero, for S = {1}, for N = 0, and
when S contains zero (then C and its Tor objects are zero).
(blueprint: lem-pc-tor-localization-denominators)
-/
theorem tor_localization_denominators
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) [Algebra B C] (S : Submonoid B) [IsLocalization S C]
    (N : ModuleCat.{u} A) (j : ℕ)
    (f : (restrictScalars φ).obj (of B B) ⟶
      (restrictScalars ((algebraMap B C).comp φ)).obj (of C C))
    (hf : ∀ b : B, f b = algebraMap B C b)
    (x : (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars ((algebraMap B C).comp φ)).obj (of C C))).obj N)) :
    ∃ u : Cˣ, ∃ y : (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars φ).obj (of B B))).obj N),
      (((Tor' (ModuleCat.{u} A) j).map
        ((restrictScalars ((algebraMap B C).comp φ)).map
          (u.mulLeftLinearEquiv C C).toModuleIso.hom)).app N) x =
        (((Tor' (ModuleCat.{u} A) j).map f).app N) y := by
  classical
  obtain ⟨σ⟩ := nonempty_tor'_flip_iso A j
  let P := projectiveResolution N
  let H := HomologicalComplex.homologyFunctor (ModuleCat A) (.down ℕ) j
  let e (M : ModuleCat.{u} A) :=
    (σ.app M).app N ≪≫ P.isoLeftDerivedObj (MonoidalCategory.tensorRight M) j
  have naturality {M M' : ModuleCat.{u} A} (g : M ⟶ M') :
      (((Tor' (ModuleCat A) j).map g).app N) ≫ (e M').hom =
        (e M).hom ≫ H.map
          ((NatTrans.mapHomologicalComplex
            ((MonoidalCategory.tensoringRight (ModuleCat A)).map g)
              (.down ℕ)).app P.complex) := by
    have hσ := congrArg (fun t ↦ t.app N) (σ.hom.naturality g)
    change (((Tor' (ModuleCat A) j).map g).app N) ≫ ((σ.app M').app N).hom =
      ((σ.app M).app N).hom ≫ ((Tor' (ModuleCat A) j).obj N).map g at hσ
    change _ ≫ (((σ.app M').app N).hom ≫
      (P.isoLeftDerivedObj (MonoidalCategory.tensorRight M') j).hom) = _
    rw [← Category.assoc, hσ, Category.assoc]
    change _ ≫ ((NatTrans.leftDerived
      ((MonoidalCategory.tensoringRight (ModuleCat A)).map g) j).app N ≫ _) = _
    rw [P.leftDerived_app_eq]
    simp [e, H]
  let MB := (restrictScalars φ).obj (of B B)
  let MC := (restrictScalars ((algebraMap B C).comp φ)).obj (of C C)
  obtain ⟨u, z, hz⟩ := tensor_complex_localization_denominators
    A B C φ S P.complex j f hf ((e MC).hom x)
  refine ⟨u, (e MB).inv z, ?_⟩
  apply (ModuleCat.mono_iff_injective (e MC).hom).mp inferInstance
  have hu := naturality
    ((restrictScalars ((algebraMap B C).comp φ)).map
      (u.mulLeftLinearEquiv C C).toModuleIso.hom)
  have hf' := naturality f
  have hux := congrArg (fun t ↦ t x) hu
  have hfy := congrArg (fun t ↦ t ((e MB).inv z)) hf'
  simp only [ModuleCat.comp_apply] at hux hfy
  rw [hux, hfy]
  have hez : (e MB).hom ((e MB).inv z) = z := by
    change ((e MB).inv ≫ (e MB).hom) z = z
    rw [Iso.inv_hom_id]
    rfl
  change _ = (H.map _) ((e MB).hom ((e MB).inv z))
  rw [hez]
  exact hz

end ModuleCat
