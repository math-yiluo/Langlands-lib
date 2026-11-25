/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Integral, finite-coefficient, and algebraic-closure l-adic representations

Source: Deligne, Weil II (1.1.6), and Milne, Lectures on Étale Cohomology, §19, p. 125
(blueprint: def-pod-l-adic-representations).

A representation of `G` by linear automorphisms is a monoid homomorphism `G →* (V ≃ₗ[R] V)`
with jointly continuous action map `fun p : G × V ↦ ρ p.1 p.2`, the form of the pod family
(`Padic.exists_stable_lattice`, lem-pod-profinite-stable-lattice). `E` carries the topology of
`spectralNorm.nontriviallyNormedField ℚ_[l] E` and `V` the topology `moduleTopology E V`.
Morphisms are the `R`-linear maps `f` with `f (ρ g v) = σ g (f v)` (`IsEquivariant`); tensor
products carry the diagonal action (`tensorDiagonal`); the unit is `R` with the trivial action
`1 : G →* (R ≃ₗ[R] R)`.
-/

@[expose] public section

universe u v w z
open scoped TensorProduct

namespace Representation

/-- A continuous integral representation is finite over the coefficient ring and has continuous
joint action for its maximal-ideal-adic module topology. Source: Milne, LEC §19, p. 125,
and Weil II (1.1.6) (blueprint: def-pod-l-adic-representations). -/
def IsContinuousIntegral (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (G : ProfiniteGrp.{v})
    (M : Type w) [AddCommGroup M] [Module (Padic.coefficientExtensionIntegers l E) M]
    (ρ : G →* (M ≃ₗ[Padic.coefficientExtensionIntegers l E] M)) : Prop :=
  Module.Finite (Padic.coefficientExtensionIntegers l E) M ∧
    letI := (Padic.coefficientExtensionMaximalIdeal l E).adicModuleTopology M
    Continuous (fun p : G × M ↦ ρ p.1 p.2)

/-- A continuous finite-coefficient representation is finite-dimensional, with continuous joint
action for the module topology over the spectral-norm topology of `E`. Source: Milne, LEC §19,
p. 125, and Weil II (1.1.6) (blueprint: def-pod-l-adic-representations). -/
def IsContinuousCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module E V] (ρ : G →* (V ≃ₗ[E] V)) : Prop :=
  FiniteDimensional E V ∧
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI : TopologicalSpace V := moduleTopology E V
    Continuous (fun p : G × V ↦ ρ p.1 p.2)

/-- An l-adic representation descends to a continuous representation on a finite-extension
structure inside `V`. The scalar-extension equivalence is required to be the canonical map
`a ⊗ v ↦ a • v`, so an arbitrary isomorphism cannot serve as a descent witness.
Source: Deligne, Weil II (1.1.6) (blueprint: def-pod-l-adic-representations). -/
def IsLAdic (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (G : ProfiniteGrp.{v}) (V : Type w)
    [AddCommGroup V] [Module Ω V] (ρ : G →* (V ≃ₗ[Ω] V)) : Prop :=
  FiniteDimensional Ω V ∧
    ∃ (E : IntermediateField ℚ_[l] Ω) (_ : FiniteDimensional ℚ_[l] E),
      letI := Module.compHom V (algebraMap E Ω)
      ∃ (W : Submodule E V) (τ : G →* (W ≃ₗ[E] W)),
        IsContinuousCoefficient l E G W τ ∧
        (∀ (g : G) (x : W), (τ g x : V) = ρ g (x : V)) ∧
        ∃ e : (Ω ⊗[E] W) ≃ₗ[Ω] V,
          ∀ (a : Ω) (x : W), e (a ⊗ₜ[E] x) = a • (x : V)

/-- A morphism of representations is a linear map commuting with the actions.
Source: Deligne, Weil II (1.1.6) (blueprint: def-pod-l-adic-representations). -/
def IsEquivariant (R : Type u) [CommRing R] (G : Type z) [Group G]
    (V : Type v) [AddCommGroup V] [Module R V] (W : Type w) [AddCommGroup W] [Module R W]
    (ρ : G →* (V ≃ₗ[R] V)) (σ : G →* (W ≃ₗ[R] W)) (f : V →ₗ[R] W) : Prop :=
  ∀ (g : G) (x : V), f (ρ g x) = σ g (f x)

/-- The diagonal action `g ↦ ρ g ⊗ σ g` on `V ⊗[R] W` (Mathlib's `Representation.tprod`,
read through `LinearMap.GeneralLinearGroup.generalLinearEquiv`).
Source: Deligne, Weil II (1.1.6) (blueprint: def-pod-l-adic-representations). -/
noncomputable def tensorDiagonal (R : Type u) [CommRing R] (G : Type z) [Group G]
    (V : Type v) [AddCommGroup V] [Module R V] (W : Type w) [AddCommGroup W] [Module R W]
    (ρ : G →* (V ≃ₗ[R] V)) (σ : G →* (W ≃ₗ[R] W)) : G →* ((V ⊗[R] W) ≃ₗ[R] (V ⊗[R] W)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R (V ⊗[R] W)).toMonoidHom.comp
    (Representation.asGroupHom (Representation.tprod
      ((Units.coeHom _).comp
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm.toMonoidHom.comp ρ))
      ((Units.coeHom _).comp
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv R W).symm.toMonoidHom.comp σ))))

/-- Extension of coefficients carries the action `1 ⊗ σ` on `L ⊗[E] V`, canonically the
same as `σ ⊗ 1` on `V ⊗[E] L` via the tensor flip. For the node this is used when
`E ⊆ L` are finite subextensions. Source: Deligne, Weil II (1.1.6), coefficient extension,
and (1.1.1)(d) (blueprint: def-pod-l-adic-representations). -/
noncomputable def coefficientScalarExtension (E : Type u) [Field E] (L : Type v) [Field L]
    [Algebra E L] (G : Type z) [Group G] (V : Type w) [AddCommGroup V] [Module E V]
    (ρ : G →* (V ≃ₗ[E] V)) : G →* ((L ⊗[E] V) ≃ₗ[L] (L ⊗[E] V)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv L (L ⊗[E] V)).toMonoidHom.comp
    ((Units.map (Module.End.baseChangeHom E L V).toMonoidHom).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm.toMonoidHom.comp ρ))

end Representation
