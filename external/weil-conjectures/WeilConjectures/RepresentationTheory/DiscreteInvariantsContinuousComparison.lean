/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.RepresentationTheory.DiscreteResolutionContinuousCohomology
public import WeilConjectures.RepresentationTheory.ContinuousCohomologyCoefficientEquiv

/-!
# Derived invariants and homogeneous continuous cohomology

Source: Stacks Project, Etale Cohomology, Section 0DVG.
(blueprint: lem-sc-discrete-invariants-continuous-comparison).
-/

@[expose] public section

universe u v w s t

open CategoryTheory

namespace Rep

/-- Additive equivalence between derived invariants transported across an abelian equivalence
and homogeneous continuous cohomology, including a change of coefficient universe.

Source: Stacks Project, Etale Cohomology, Section 0DVG, profinite comparison.
(blueprint: lem-sc-discrete-invariants-continuous-comparison).

Proof: Transport an injective resolution of F across E. An equivalence preserves
injectives and is exact. The given natural isomorphism identifies its Gamma complex
with the invariant complex of the transported resolution. Continuous inhomogeneous
cochains on discrete modules form an exact cohomological delta-functor: continuous
functions on compact powers have finite image, so a surjection of discrete modules
allows a continuous lift, chosen separately for each value. Embed a module M into
locally constant functions G -> M by m |-> (x |-> x*m), with right-translation action.
Such functions have open stabilizers: a finite clopen partition has a common open
stabilizing subgroup. In positive degrees the insertion operator
h(F)(g1,...,g(n-1))(x) = F(x,g1,...,g(n-1))(1) contracts its continuous cochain complex.
All maps are continuous, using finite clopen partitions on compact finite powers.
This effaces positive cohomology. The resulting delta-functor and derived invariants
are universal and agree in degree zero; uniqueness gives inverse comparisons.
Finally, the compact-open exponential law identifies iterated continuous maps with
jointly continuous maps. Evaluate an equivariant homogeneous cochain at
(1,g1,g1*g2,...,g1*...*gn). The inverse is
(g0,...,gn) |-> g0*c(g0^-1*g1,...,g(n-1)^-1*gn). Alternating omission becomes the
inhomogeneous differential, by expanding the recursive homogeneous differential.
The equivariant linear equivalence e transports these complexes, including between
universes. Kernel modulo image computes the underlying TopModuleCat homology, so
these inverse cochain transformations descend to the claimed additive equivalence.
The representation universe is at least the group universe so coinduced modules
remain in the same category. No finite-ring assumption is used: the scalar ring is the
discrete integers. -/
noncomputable def rightDerivedAddEquivContinuousCohomology
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A] [HasInjectiveResolutions A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (Γ : A ⥤ AddCommGrpCat.{max u s}) [Γ.Additive]
    (η : Γ ≅ E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat)
    (F : A) (N : TopRep.{max u t} ℤ G) [DiscreteTopology N.V]
    (e : (E.functor.obj F).obj.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : (E.functor.obj F).obj.V),
      e ((E.functor.obj F).obj.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    (Γ.rightDerived q).obj F ≃+ continuousCohomology q N := by
  classical
  let V := E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat
  let _ : V.Additive := Functor.additive_of_iso η
  let I := injectiveResolution F
  let : TopologicalSpace (E.functor.obj F).obj.V := ⊥
  let : DiscreteTopology (E.functor.obj F).obj.V := ⟨rfl⟩
  -- The Rep module structure is not the `zsmul` one, so its scalar action is made
  -- continuous directly from the discrete topology.
  let : @ContinuousSMul ℤ (E.functor.obj F).obj.V (E.functor.obj F).obj.hV2.toSMul _ _ :=
    @ContinuousSMul.mk ℤ _ (E.functor.obj F).obj.hV2.toSMul _ _ continuous_of_discreteTopology
  let ρ : ContRepresentation ℤ G (E.functor.obj F).obj.V :=
    .ofMonoidHom
      { toFun := fun g ↦ ⟨(E.functor.obj F).obj.ρ g, continuous_of_discreteTopology⟩
        map_one' := by
          ext x
          change (E.functor.obj F).obj.ρ 1 x = x
          simp
        map_mul' := by
          intro g h
          ext x
          change (E.functor.obj F).obj.ρ (g * h) x =
            (E.functor.obj F).obj.ρ g ((E.functor.obj F).obj.ρ h x)
          simp [map_mul] }
  let M : TopRep.{max u s} ℤ G := TopRep.of ρ
  -- The coefficient identity, from the Rep `ℤ`-module structure to the `zsmul` one on `M`.
  let e₀ : @LinearEquiv ℤ ℤ _ _ (RingHom.id ℤ) (RingHom.id ℤ) _ _ (E.functor.obj F).obj.V M.V
      _ _ _ (AddCommGroup.toIntModule M.V) :=
    @LinearEquiv.mk ℤ ℤ _ _ _ _ _ _ _ _ _ _ _ (AddCommGroup.toIntModule M.V)
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) _ _ _ _ _ (AddCommGroup.toIntModule M.V)
        ⟨id, fun _ _ ↦ rfl⟩ fun n x ↦ int_smul_eq_zsmul _ n x) id (fun _ ↦ rfl) (fun _ ↦ rfl)
  let a := invariantResolutionHomologyAddEquivContinuousCohomology
    G A E F I M e₀ (fun _ _ ↦ rfl) q
  let b := continuousCohomologyAddEquivOfCoefficients G M N (e₀.symm ≪≫ₗ e) he q
  let c := (I.isoRightDerivedObj Γ q) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).mapIso
      ((NatIso.mapHomologicalComplex η (ComplexShape.up ℕ)).app I.cocomplex)
  exact c.addCommGroupIsoToAddEquiv.trans (a.trans b)

end Rep
