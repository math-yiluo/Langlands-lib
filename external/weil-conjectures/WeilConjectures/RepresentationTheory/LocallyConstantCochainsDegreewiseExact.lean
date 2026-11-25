/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.LocallyConstant.Algebra
import WeilConjectures.RepresentationTheory.OpenStabilizerAdjunction
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Degreewise exactness of locally constant cochains
Source: Stacks Project, Tag 0DVG.
(blueprint: lem-sc-locally-constant-cochains-degreewise-exact).
-/
@[expose] public section
universe u v w s
open CategoryTheory
namespace Rep
/-- Source: Stacks Project, Tag 0DVG, proof of degreewise exactness.
(blueprint: lem-sc-locally-constant-cochains-degreewise-exact).
Proof: The open-stabilizer adjunction of Stacks Tag 04JF makes the inclusion
into representations a left adjoint preserving monomorphisms. Compose it with
E and the forgetful functors to integer modules and abelian groups. This
composite preserves finite colimits and monomorphisms, hence homology by
Mathlib. It is additive because it preserves zero morphisms and binary
biproducts. Thus the underlying coefficient sequence is short exact.
The first cochain map is injective pointwise. Its image equals the kernel of
the second: choose a preimage through the first map at each value in that
kernel. For surjectivity of the second cochain map, choose a lift of each
value of a locally constant cochain through the coefficient surjection.
Postcomposition with this set-theoretic choice preserves local constancy,
since a cochain is constant on an open neighborhood of every point.
The coefficient-map formula hm and the additive equivalences e transport
these three assertions to the evaluation of S.map C in AddCommGrpCat.
Thus the resulting short complex is short exact in every degree. -/
theorem locallyConstantCochains_degreewise_exact
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hm : ∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
      e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g))
    [C.Additive] :
    ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
      ((S.map C).map (HomologicalComplex.eval
        AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n)).ShortExact := by
  classical
  let U := ModuleCat.forgetDiscreteGModule.{0, u, max u s} ℤ G
  obtain ⟨_, _, hmono, R, adj, _⟩ :=
    ModuleCat.openStabilizerAdjunction.{0, u, max u s} ℤ G
  let : U.IsLeftAdjoint := adj.isLeftAdjoint
  let : U.PreservesMonomorphisms := ⟨fun f _ ↦ hmono f inferInstance⟩
  let F : A ⥤ AddCommGrpCat.{max u s} := E.functor ⋙ U ⋙
    (Rep.hasForgetToModuleCat (k := ℤ) (G := G)).forget₂ ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat
  have : CategoryTheory.Limits.PreservesFiniteColimits F := by
    dsimp [F]
    infer_instance
  have : F.PreservesMonomorphisms := by
    dsimp [F]
    infer_instance
  have : F.PreservesZeroMorphisms := inferInstance
  have : CategoryTheory.Limits.PreservesBinaryBiproducts F :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels F
  intro S hS n
  have := hS.mono_f
  have := hS.epi_g
  have hT := hS.map F
  let T := (S.map C).map (HomologicalComplex.eval
    AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n)
  have hf : Function.Injective (E.functor.map S.f).hom.hom := hT.ab_injective_f
  have hg : Function.Surjective (E.functor.map S.g).hom.hom := hT.ab_surjective_g
  have hex : ∀ y : (E.functor.obj S.X₂).obj.V,
      (E.functor.map S.g).hom.hom y = 0 →
      ∃ x : (E.functor.obj S.X₁).obj.V, (E.functor.map S.f).hom.hom x = y :=
    (ShortComplex.ab_exact_iff (S.map F)).1 hT.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.ab_exact_iff T).2
    intro x hx
    let lift : (E.functor.obj S.X₂).obj.V → (E.functor.obj S.X₁).obj.V :=
      fun y ↦ if hy : (E.functor.map S.g).hom.hom y = 0 then
        Classical.choose (hex y hy) else 0
    refine ⟨(e S.X₁ n).symm ((e S.X₂ n x).map lift), ?_⟩
    apply (e S.X₂ n).injective
    ext g
    change e S.X₂ n (((C.map S.f).f n)
      ((e S.X₁ n).symm ((e S.X₂ n x).map lift))) g = e S.X₂ n x g
    rw [hm, AddEquiv.apply_symm_apply]
    have hy : (E.functor.map S.g).hom.hom (e S.X₂ n x g) = 0 := by
      rw [← hm]
      change e S.X₃ n (T.g x) g = 0
      rw [hx, map_zero]
      rfl
    change (E.functor.map S.f).hom.hom (lift (e S.X₂ n x g)) = e S.X₂ n x g
    simp only [lift, dite_eq_left hy]
    exact Classical.choose_spec (hex _ hy)
  · apply (AddCommGrpCat.mono_iff_injective T.f).2
    intro x y hxy
    apply (e S.X₁ n).injective
    ext g
    apply hf
    rw [← hm, ← hm]
    exact congrArg (fun z ↦ e S.X₂ n z g) hxy
  · apply (AddCommGrpCat.epi_iff_surjective T.g).2
    intro x
    let lift := Function.surjInv hg
    refine ⟨(e S.X₂ n).symm ((e S.X₃ n x).map lift), ?_⟩
    apply (e S.X₃ n).injective
    ext g
    change e S.X₃ n (((C.map S.g).f n)
      ((e S.X₂ n).symm ((e S.X₃ n x).map lift))) g = e S.X₃ n x g
    rw [hm, AddEquiv.apply_symm_apply]
    exact Function.surjInv_eq hg _

end Rep
