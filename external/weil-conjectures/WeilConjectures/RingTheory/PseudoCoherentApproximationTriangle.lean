/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
import WeilConjectures.RingTheory.DerivedMapLift
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite-free approximation triangles

Source: Stacks Project, Tag 064R, first half of the proof of assertion (1).
(blueprint: lem-pc-ring-pseudo-coherent-approximation-triangle).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

private theorem truncIndex (n i : ℤ) (hi : n ≤ i) :
    (ComplexShape.embeddingUpIntGE n).f (i - n).toNat = i := by
  simp only [ComplexShape.embeddingUpIntGE_f]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- Brutally truncate a finite-free approximation below its cutoff.
Source: Stacks Project, Tag 064R, first sentence of the proof of (1).
The inclusion is degreewise an isomorphism from the cutoff onward. Apply the
short-complex homology comparison above the cutoff and the cycles comparison
at the cutoff, then transport along `homologyFunctorFactors` and compose with
 the original approximation. The calculation is also used in
`PseudoCoherentIffAllM`, which cannot be imported here because it depends on
 the present theorem. -/
private theorem exists_truncated_approximation {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (n : ℤ) (A : DerivedCategory (ModuleCat.{v} R)) (hA : IsMPseudoCoherent n A) :
    ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ),
      P.IsStrictlyGE n ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      ∃ f : Q.obj P ⟶ A,
        (∀ i : ℤ, n < i → IsIso ((homologyFunctor (ModuleCat.{v} R) i).map f)) ∧
        Epi ((homologyFunctor (ModuleCat.{v} R) n).map f) := by
  obtain ⟨E, a, b, ha, hb, hfree, g, hg, hepi⟩ := hA
  have := hb
  let P := E.stupidTrunc (ComplexShape.embeddingUpIntGE n)
  let f := E.ιStupidTrunc (ComplexShape.embeddingUpIntGE n)
  have hf (i : ℤ) (hi : n ≤ i) : IsIso (f.f i) :=
    E.isIso_ιStupidTrunc_f _ (truncIndex n i hi)
  have hPfree : ∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i) := by
    intro i
    by_cases hi : n ≤ i
    · have := (hfree i).1
      have := (hfree i).2
      let e := (E.stupidTruncXIso _ (truncIndex n i hi)).symm.toLinearEquiv
      exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
    · have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero
        (E.isZero_stupidTrunc_X _ i (by
          intro k hk
          simp only [ComplexShape.embeddingUpIntGE_f] at hk
          omega))
      exact ⟨inferInstance, inferInstance⟩
  refine ⟨P, b, inferInstance, inferInstance, hPfree, Q.map f ≫ g, ?_, ?_⟩
  · intro i hi
    have hprev : IsIso (f.f ((ComplexShape.up ℤ).prev i)) := hf _ (by simp; omega)
    have hmid : IsIso (f.f i) := hf i (by omega)
    have hnext : IsIso (f.f ((ComplexShape.up ℤ).next i)) := hf _ (by simp; omega)
    have hhom : IsIso (HomologicalComplex.homologyMap f i) := by
      change IsIso (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (.up ℤ) i).map f))
      exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
        (show Epi (f.f ((ComplexShape.up ℤ).prev i)) from inferInstance)
        hmid (show Mono (f.f ((ComplexShape.up ℤ).next i)) from inferInstance)
    have := hhom
    have hn := homologyFunctorFactors_hom_naturality f i
    have : IsIso ((homologyFunctor (ModuleCat.{v} R) i).map (Q.map f) ≫
        (homologyFunctorFactors (ModuleCat.{v} R) i).hom.app E) := by
      rw [hn]
      infer_instance
    have : IsIso ((homologyFunctor (ModuleCat.{v} R) i).map (Q.map f)) :=
      IsIso.of_isIso_comp_right _ ((homologyFunctorFactors (ModuleCat.{v} R) i).hom.app E)
    have := hg i hi
    rw [Functor.map_comp]
    infer_instance
  · have hmid : IsIso (f.f n) := hf n le_rfl
    have hnext : IsIso (f.f ((ComplexShape.up ℤ).next n)) := hf _ (by simp)
    have hhom : Epi (HomologicalComplex.homologyMap f n) := by
      change Epi (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (.up ℤ) n).map f))
      apply ShortComplex.epi_homologyMap_of_epi_cyclesMap'
      have hc := ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (.up ℤ) n).map f)
        hmid (show Mono (f.f ((ComplexShape.up ℤ).next n)) from inferInstance)
      have := hc
      infer_instance
    have := hhom
    have hn := homologyFunctorFactors_hom_naturality f n
    have : Epi ((homologyFunctor (ModuleCat.{v} R) n).map (Q.map f) ≫
        (homologyFunctorFactors (ModuleCat.{v} R) n).hom.app E) := by
      rw [hn]
      infer_instance
    have : Epi ((homologyFunctor (ModuleCat.{v} R) n).map (Q.map f)) :=
      (epi_comp_iff_of_isIso _
        ((homologyFunctorFactors (ModuleCat.{v} R) n).hom.app E)).mp inferInstance
    have := hepi
    rw [Functor.map_comp]
    infer_instance

/-- A compatible finite-free triangle, before checking cohomology on its third vertex.
Source: Stacks Project, Tag 064R, proof of assertion (1), through construction of
 the morphism of distinguished triangles.
(blueprint: lem-pc-ring-pseudo-coherent-approximation-triangle).

Proof: choose the finite-free witnesses for the first two vertices. Brutally truncate
 the first witness below `m + 1`; its cohomology above `m + 1` is unchanged, and its
 cohomology in degree `m + 1` surjects onto that of the original witness. The truncated
 complex is bounded finite free and vanishes below `m`. Finite free modules are
 projective. Apply the derived map lift (Tag 064E) to lift the composite to the second
 witness as a chain map. Its mapping cone is bounded finite free: each term is the
 direct sum of a term of the second witness and a shifted term of the first witness.
 The cone triangle is distinguished. TR3 extends the commuting square to a morphism
 of triangles. Its first two components retain exactly the witness conditions.
 This statement makes no assertion about cohomology of the third component. -/
theorem exists_pseudoCoherent_approximation_triangle
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R)))
    (hA : IsMPseudoCoherent (m + 1) T.obj₁)
    (hB : IsMPseudoCoherent m T.obj₂) :
    ∃ (E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) ∧
      ∃ (S : Triangle (DerivedCategory (ModuleCat.{v} R))) (φ : S ⟶ T),
        S ∈ distTriang (DerivedCategory (ModuleCat.{v} R)) ∧ S.obj₃ = Q.obj E ∧
        (∀ i : ℤ, m + 1 < i →
          IsIso ((homologyFunctor (ModuleCat.{v} R) i).map φ.hom₁)) ∧
        Epi ((homologyFunctor (ModuleCat.{v} R) (m + 1)).map φ.hom₁) ∧
        (∀ i : ℤ, m < i →
          IsIso ((homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂)) ∧
        Epi ((homologyFunctor (ModuleCat.{v} R) m).map φ.hom₂) := by
  obtain ⟨P, bP, hPge, hPle, hPfree, f, hf, hfepi⟩ :=
    exists_truncated_approximation (m + 1) T.obj₁ hA
  obtain ⟨F, aF, bF, hFge, hFle, hFfree, g, hg, hgepi⟩ := hB
  have := hPge
  have := hPle
  have := hFge
  have := hFle
  have hprojective (i : ℤ) : Projective (P.X i) := by
    have := (hPfree i).1
    infer_instance
  let L := Q.objPreimage T.obj₂
  let e : Q.obj L ≅ T.obj₂ := Q.objObjPreimageIso T.obj₂
  let α : Q.obj F ⟶ Q.obj L := g ≫ e.inv
  let β : Q.obj P ⟶ Q.obj L := f ≫ T.mor₁ ≫ e.inv
  have hαiso (i : ℤ) (hi : m < i) :
      IsIso ((homologyFunctor (ModuleCat.{v} R) i).map α) := by
    have := hg i hi
    dsimp [α]
    rw [Functor.map_comp]
    infer_instance
  have hαepi : Epi ((homologyFunctor (ModuleCat.{v} R) m).map α) := by
    have := hgepi
    dsimp [α]
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨γ, hγ⟩ := RingTheory.derived_map_lift R m P F L
    ⟨m + 1, bP, hPge, hPle⟩ hprojective
    (fun i hi ↦ P.isZero_of_isStrictlyGE (m + 1) i (by omega)) α β hαiso hαepi
  have comm : Q.map γ ≫ g = f ≫ T.mor₁ := by
    apply (cancel_mono e.inv).mp
    simpa only [α, β, Category.assoc] using hγ
  let E := CochainComplex.mappingCone γ
  have hEge : E.IsStrictlyGE (min m aF) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P.isZero_of_isStrictlyGE (m + 1) _ (by omega),
      F.isZero_of_isStrictlyGE aF _ (by omega)⟩
  have hEle : E.IsStrictlyLE (max (bP - 1) bF) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P.isZero_of_isStrictlyLE bP _ (by omega),
      F.isZero_of_isStrictlyLE bF _ (by omega)⟩
  have hEfree (i : ℤ) : Module.Free R (E.X i) ∧ Module.Finite R (E.X i) := by
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod γ i (i + 1) rfl ≪≫
      ModuleCat.biprodIsoProd (P.X (i + 1)) (F.X i)
    have := (hPfree (i + 1)).1
    have := (hPfree (i + 1)).2
    have := (hFfree i).1
    have := (hFfree i).2
    exact ⟨Module.Free.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩
  let S := Q.mapTriangle.obj (CochainComplex.mappingCone.triangle γ)
  have hS : S ∈ distTriang (DerivedCategory (ModuleCat.{v} R)) :=
    mappingCone_triangle_distinguished γ
  obtain ⟨h, hcomm₂, hcomm₃⟩ :=
    complete_distinguished_triangle_morphism S T hS hT f g comm
  let φ : S ⟶ T :=
    { hom₁ := f
      hom₂ := g
      hom₃ := h
      comm₁ := comm
      comm₂ := hcomm₂
      comm₃ := hcomm₃ }
  exact ⟨E, min m aF, max (bP - 1) bF, hEge, hEle, hEfree,
    S, φ, hS, rfl, hf, hfepi, hg, hgepi⟩

end DerivedCategory
