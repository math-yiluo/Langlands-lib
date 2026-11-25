/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Injective resolutions of diagrams of bounded below complexes

Let `C` be a Grothendieck abelian category and `J` a small category. The functor category
`J ⥤ C` is again Grothendieck abelian (`CategoryTheory.Functor.isGrothendieckAbelian`), hence
has enough injectives, and the evaluation functors preserve injective objects, their left
adjoints `X ↦ ∐_{j ⟶ k} X` preserving monomorphisms
(`CategoryTheory.Injective.functor_obj`).

Viewing a diagram `F : J ⥤ CochainComplex C ℤ` as a complex of diagrams
(`CategoryTheory.Functor.complexOfFunctors`), a bounded below injective resolution in `J ⥤ C`
gives a *functorial* resolution of `F`: a natural transformation `F ⟶ I` which is a
quasi-isomorphism at every `j`, where every `I.obj j` is strictly concentrated in the same degrees
as the `F.obj j` and has injective terms
(`CategoryTheory.Functor.exists_quasiIso_injective_of_isStrictlyGE`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace CategoryTheory

namespace Limits

/-- In an abelian category with exact coproducts of shape `ι`, a coproduct of monomorphisms is a
monomorphism. -/
lemma mono_sigmaMap {C : Type*} [Category* C] [Abelian C] {ι : Type*}
    [HasCoproductsOfShape ι C] [HasExactColimitsOfShape (Discrete ι) C]
    {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) [∀ i, Mono (f i)] : Mono (Limits.Sigma.map f) := by
  have : Mono (Discrete.natTrans (F := Discrete.functor X) (G := Discrete.functor Y)
      (fun i ↦ f i.as)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro i
    dsimp
    infer_instance
  exact (colim (J := Discrete ι) (C := C)).map_mono
    (Discrete.natTrans (F := Discrete.functor X) (G := Discrete.functor Y) (fun i ↦ f i.as))

end Limits

namespace Functor

variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (J : Type w) [SmallCategory J]

/-- The category of diagrams of a small shape in a Grothendieck abelian category is Grothendieck
abelian: filtered colimits are computed pointwise, and a separator is given by
`Presheaf.hasSeparator`. -/
instance isGrothendieckAbelian : IsGrothendieckAbelian.{w} (J ⥤ C) where
  ab5OfSize := ⟨fun _ _ _ ↦ inferInstance⟩
  hasSeparator := HasSeparator.of_equivalence ((opOpEquivalence J).congrLeft (E := C))

/-- The left adjoint `X ↦ ∐_{j ⟶ k} X` of the evaluation at `j` preserves monomorphisms, coproducts
being exact in a Grothendieck abelian category. -/
instance preservesMonomorphisms_evaluationLeftAdjoint (j : J) :
    (evaluationLeftAdjoint C j).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    rw [NatTrans.mono_iff_mono_app]
    intro k
    have : ((evaluationLeftAdjoint C j).map f).app k =
        Limits.Sigma.map (fun _ : j ⟶ k ↦ f) := by
      refine Sigma.hom_ext _ _ fun g ↦ ?_
      rw [evaluationLeftAdjoint_map_app]
      erw [Sigma.ι_comp_desc]
    rw [this]
    exact mono_sigmaMap _

variable {J}

/-- The values of an injective diagram in a Grothendieck abelian category are injective. -/
lemma _root_.CategoryTheory.Injective.functor_obj (I : J ⥤ C) [Injective I] (j : J) :
    Injective (I.obj j) :=
  Injective.injective_of_adjoint (evaluationAdjunctionRight C j) I

/-- A diagram of complexes, viewed as a complex of diagrams. -/
@[simps]
def complexOfFunctors {ι : Type*} {c : ComplexShape ι} (F : J ⥤ HomologicalComplex C c) :
    HomologicalComplex (J ⥤ C) c where
  X i := F ⋙ HomologicalComplex.eval C c i
  d i j := Functor.whiskerLeft F (HomologicalComplex.dNatTrans C c i j)
  shape i j h := by
    ext t
    exact (F.obj t).shape i j h
  d_comp_d' i j k _ _ := by
    ext t
    exact (F.obj t).d_comp_d i j k

/-- **Functorial injective resolutions of diagrams of bounded below complexes.** For a diagram
`F` of complexes strictly concentrated in degrees `≥ a` in a Grothendieck abelian category, there
is a natural transformation `F ⟶ I` which is a quasi-isomorphism at every `j`, where every
`I.obj j` is strictly concentrated in degrees `≥ a` and has injective terms. -/
lemma exists_quasiIso_injective_of_isStrictlyGE (F : J ⥤ CochainComplex C ℤ) (a : ℤ)
    [∀ j, (F.obj j).IsStrictlyGE a] :
    ∃ (I : J ⥤ CochainComplex C ℤ) (ι : F ⟶ I), (∀ j, QuasiIso (ι.app j)) ∧
      (∀ j, (I.obj j).IsStrictlyGE a) ∧ ∀ j n, Injective ((I.obj j).X n) := by
  have : CochainComplex.IsStrictlyGE (complexOfFunctors F) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.isZero _ fun j ↦ (F.obj j).isZero_of_isStrictlyGE a i hi
  obtain ⟨L, ι, hι, hL, _⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (complexOfFunctors F) a
  refine ⟨L.asFunctor, { app j := { f n := (ι.f n).app j, comm' n m _ := ?_ }, naturality := ?_ },
    fun j ↦ ?_, fun j ↦ ?_, fun j n ↦ Injective.functor_obj _ j⟩
  · exact NatTrans.congr_app (ι.comm n m) j
  · intro j k g
    ext n
    exact (ι.f n).naturality g
  · exact (HomologicalComplex.quasiIso_iff_evaluation ι).1 hι j
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (L.isZero_of_isStrictlyGE a i hi).obj j

end Functor

end CategoryTheory
