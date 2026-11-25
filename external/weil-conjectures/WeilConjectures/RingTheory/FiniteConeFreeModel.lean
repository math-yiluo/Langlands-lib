/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free
import WeilConjectures.RingTheory.FiniteConeFreeExtension
import WeilConjectures.RingTheory.StabilizingConeTower

/-!
# Finite obstruction groups give a finite free model

Source: Stacks Project, More on Algebra, Tag 064U, descending construction.
(blueprint: lem-pc-ring-finite-cone-free-model).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Data of a single bounded approximation, with an exact cone above its cutoff. -/
private structure ConeApproximation (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (b n : ℤ) where
  complex : CochainComplex (ModuleCat.{v} R) ℤ
  map : complex ⟶ C
  lower : complex.IsStrictlyGE n
  upper : complex.IsStrictlyLE b
  finiteFree : ∀ i : ℤ, Module.Free R (complex.X i) ∧ Module.Finite R (complex.X i)
  vanishing : ∀ i : ℤ, n ≤ i → IsZero
    ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone map)))

/-- The cone of a map from the zero complex is isomorphic to its target. -/
private theorem zero_cone_inr_isIso (R : Type u) [CommRing R]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) :
    IsIso (CochainComplex.mappingCone.inr
      (0 : (HomologicalComplex.zero : CochainComplex (ModuleCat.{v} R) ℤ) ⟶ C)) := by
  let Z : CochainComplex (ModuleCat.{v} R) ℤ := HomologicalComplex.zero
  let f : Z ⟶ C := 0
  have hZ (i : ℤ) : IsZero (Z.X i) :=
    (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map_isZero
      (HomologicalComplex.isZero_zero)
  have (i : ℤ) : IsIso ((CochainComplex.mappingCone.inr f).f i) := by
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl
    have h : IsIso (biprod.inr : C.X i ⟶ Z.X (i + 1) ⊞ C.X i) :=
      (isoZeroBiprod (hZ (i + 1))).isIso_hom
    have he : (CochainComplex.mappingCone.inr f).f i ≫ e.hom =
        (biprod.inr : C.X i ⟶ Z.X (i + 1) ⊞ C.X i) :=
      HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom f (i + 1) i rfl
    apply (isIso_comp_right_iff _ e.hom).1
    rw [he]
    exact h
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Construct a bounded above finite free model from finite top cohomology of the cones
of bounded finite free approximations. The ring fits in the module universe, so finite
free modules on finite sets of generators can be constructed in that universe.

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U, construction in the
proof of (2) implies (1), after the finite obstruction group has been established.
(blueprint: lem-pc-ring-finite-cone-free-model).

Proof: start at degree `b + 1` with the zero complex and the zero map to `C`. Since
`H^i(C) = 0` for `i > b`, this map is an isomorphism above `b + 1` and surjective at
`b + 1`. Suppose `F` is zero below `n` and above `b`, is finite free termwise, and its
map to `C` is an isomorphism above `n` and surjective at `n`. The cone long exact
sequence makes the cone zero in cohomology above `n - 1`. Its degree-`n - 1`
cohomology is finite by `hcone`. Choose finitely many generating classes and represent
them by cone cycles. A cone cycle is a pair in `F^n` and `C^(n - 1)` satisfying the
cycle and chain-map equations. Adjoin a finite free module in degree `n - 1`, mapping
its basis to these pairs (with the sign prescribed by the cone convention). The
cohomology sequence shows that this kills the kernel in degree `n` and covers the
cokernel in degree `n - 1`, giving an isomorphism at `n` and a surjection at `n - 1`.
All terms, maps and differentials in degrees at least `n` remain unchanged.
Use dependent choice to iterate these compatible extensions for `n = b + 1 - k`.
Apply `exists_model_of_stabilizing_cone_tower`, which constructs the degreewise
colimit complex and a quasi-isomorphism to C. In each degree an inclusion from a
sufficiently late stage is invertible. Transport finite freeness and the upper support
bound across those termwise isomorphisms. The zero ring and an acyclic C are covered
by the same construction, with empty generating sets when the obstruction is zero.
The only postponed part is `exists_finiteFree_cone_extension`, the single finite
extension step; no object is defined by selecting a witness of this postponed theorem. -/
theorem exists_finiteFree_model_of_finite_cones (R : Type u) [CommRing R] [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj C)))
    (hcone : ∀ (F : CochainComplex (ModuleCat.{v} R) ℤ) (a c : ℤ),
      F.IsStrictlyGE a → F.IsStrictlyLE c →
      (∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i)) →
      ∀ (f : F ⟶ C) (n : ℤ),
        (∀ i : ℤ, n < i → IsZero
          ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone f)))) →
        Module.Finite R
          ((homologyFunctor (ModuleCat.{v} R) n).obj (Q.obj (CochainComplex.mappingCone f)))) :
    ∃ (F : CochainComplex (ModuleCat.{v} R) ℤ), F.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i)) ∧
      ∃ f : F ⟶ C, QuasiIso f := by
  classical
  let Z : CochainComplex (ModuleCat.{v} R) ℤ := HomologicalComplex.zero
  have hZ (i : ℤ) : IsZero (Z.X i) :=
    (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) i).map_isZero
      (HomologicalComplex.isZero_zero)
  let initial : ConeApproximation R C b (b + 1) :=
    { complex := Z
      map := 0
      lower := (Z.isStrictlyGE_iff (b + 1)).2 (fun i _ => hZ i)
      upper := (Z.isStrictlyLE_iff b).2 (fun i _ => hZ i)
      finiteFree := fun i => by
        have : Subsingleton (Z.X i) := ModuleCat.subsingleton_of_isZero (hZ i)
        exact ⟨inferInstance, inferInstance⟩
      vanishing := fun i hi => by
        have := zero_cone_inr_isIso R C
        exact (hvan i (by omega)).of_iso
          ((homologyFunctor (ModuleCat.{v} R) i).mapIso
            (Q.mapIso (asIso (CochainComplex.mappingCone.inr (0 : Z ⟶ C))))).symm }
  let A (k : ℕ) := ConeApproximation R C b (b + 1 - (k : ℤ))
  have hnext (k : ℕ) (s : A k) :
      ∃ t : A (k + 1), ∃ j : s.complex ⟶ t.complex,
        j ≫ t.map = s.map ∧
          ∀ i : ℤ, b + 1 - (k : ℤ) ≤ i → IsIso (j.f i) := by
    have hfinite := hcone s.complex (b + 1 - (k : ℤ)) b s.lower s.upper
      s.finiteFree s.map (b + 1 - (k : ℤ) - 1)
      (fun i hi => s.vanishing i (by omega))
    obtain ⟨G, g, j, hl, hu, hf, hv, hc, hj⟩ :=
      exists_finiteFree_cone_extension R C s.complex s.map b (b + 1 - (k : ℤ))
        (by omega) s.lower s.upper s.finiteFree s.vanishing hfinite
    have heq : b + 1 - ((k + 1 : ℕ) : ℤ) = b + 1 - (k : ℤ) - 1 := by omega
    refine ⟨⟨G, g, ?_, hu, hf, ?_⟩, j, hc, hj⟩
    · rw [heq]
      exact hl
    · intro i hi
      exact hv i (by simpa only [heq] using hi)
  choose next inclusion hcomm hstable using hnext
  let stages : ∀ k : ℕ, A k := fun k =>
    Nat.rec (show A 0 from by simpa only [A, Nat.cast_zero, sub_zero] using initial)
      (fun k s => next k s) k
  let P (k : ℕ) := (stages k).complex
  let f (k : ℕ) : P k ⟶ C := (stages k).map
  let j (k : ℕ) : P k ⟶ P (k + 1) := inclusion k (stages k)
  obtain ⟨F, g, hg, hterms⟩ := exists_model_of_stabilizing_cone_tower R C b P f j
    (fun k => hcomm k (stages k)) (fun k => hstable k (stages k))
    (fun k => (stages k).vanishing)
  refine ⟨F, ?_, ?_, g, hg⟩
  · apply (F.isStrictlyLE_iff b).2
    intro i hi
    obtain ⟨k, ⟨e⟩⟩ := hterms i
    have := (stages k).upper
    exact ((P k).isZero_of_isStrictlyLE b i hi).of_iso e
  · intro i
    obtain ⟨k, ⟨e⟩⟩ := hterms i
    have : Module.Free R ((P k).X i) := ((stages k).finiteFree i).1
    have : Module.Finite R ((P k).X i) := ((stages k).finiteFree i).2
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv,
      Module.Finite.equiv e.symm.toLinearEquiv⟩

end DerivedCategory
