/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTower
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.RingTheory.EssentialFiniteness
import WeilConjectures.RingTheory.TensorLocalizationTowerTransition
import WeilConjectures.RingTheory.LocalizedModuleOfLiftedTensorComparison
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- Convert an already specified categorical limit system into a Noetherian local model tower.
There is no finite-presentation hypothesis and no assertion constructing a categorical system.
Source: Stacks Project, Algebra, proof of Tag 00R7, first two paragraphs, using
Tags 00QU, 00QV and 00QX for the supplied categorical system.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-categorical-conversion).

Proof: retain the index preorder and the three stage rings and stage modules of the supplied
system. Use the natural transformations for stage algebra structures and compose these maps
for the base-to-top algebra structure; restrict module scalars along them. The local structures
are supplied. Each base ring is essentially of finite type over the Noetherian ring of integers;
the middle and top rings are essentially of finite type over their preceding stages, so all
three are Noetherian. Use functor maps for transitions and compose the cocone maps with
`ULift.down` for maps into the original rings. Functor laws give the directed-system laws;
naturality gives the commutation and semilinearity clauses. The forgetful functors from
commutative rings and abelian groups to sets preserve filtered colimits. Thus every element
of each limit has a representative and equality of two representatives at one stage holds
at a later stage; composing with the lift equivalences gives the eight elementwise clauses.
The fibre transition and module transition are supplied. For the base transition, first
base-change the middle-ring transition localization along the top-stage ring, then compose
with the top-ring transition localization; tensor associativity identifies the resulting
source with the required base-to-top tensor product. For the base localization at the limit,
use tensor symmetry and the canonical module equivalence from a ring localization to its
localized module, restricting scalars to the original base ring. For module localization put
`E = S ⊗[Sᵢ] Tᵢ`, acting on `L = S ⊗[Sᵢ] Nᵢ` by the tensor action. Tensor symmetry and
transport through `ULift.down` make the supplied top-ring limit map a localization `E → S'`.
For its inverted submonoid U, localization-tensor compatibility identifies `LocalizedModule U L`
with `S' ⊗[E] L`. Tensor associativity identifies the latter with `S' ⊗[Tᵢ] Nᵢ`, and the supplied
module base-change equivalence identifies it with M. Restrict scalars to S in these equivalences.
All scalar-tower laws follow from composition and the supplied commuting squares. -/
theorem noetherian_localModelTower_of_categoricalLimit
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M] (s t : ℕ)
    (h :
      let R₁ := ULift.{max u v w} R
      let S₁ := ULift.{max u v w} S
      let T₁ := ULift.{max u v w} S'
      let α : R₁ →+* S₁ := (algebraMap R S).ulift
      let β : S₁ →+* T₁ := (algebraMap S S').ulift
      ∃ (Λ : Type (max u v w)) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
        (A Bs C : Λ ⥤ CommRingCat.{max u v w}) (ρ : A ⟶ Bs) (σ : Bs ⟶ C)
        (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R₁))
        (κ : Bs ⟶ (Functor.const Λ).obj (CommRingCat.of S₁))
        (κ' : C ⟶ (Functor.const Λ).obj (CommRingCat.of T₁))
        (D : Λ ⥤ AddCommGrpCat.{t})
        (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
        (_ : ∀ i : Λ, Module (C.obj i) (D.obj i)),
        -- local rings and local homomorphisms
        (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (Bs.obj i)) ∧
        (∀ i, IsLocalRing (C.obj i)) ∧
        (∀ i, IsLocalHom (ρ.app i).hom) ∧ (∀ i, IsLocalHom (σ.app i).hom) ∧
        (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (A.map (homOfLE h)).hom) ∧
        (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (Bs.map (homOfLE h)).hom) ∧
        (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (C.map (homOfLE h)).hom) ∧
        (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of R₁) (π.app i))) ∧
        (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S₁) (κ.app i))) ∧
        (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i))) ∧
        -- the maps to `R₁, S₁, T₁` commute with `α, β`
        (∀ i, ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α) ∧
        (∀ i, σ.app i ≫ κ'.app i = κ.app i ≫ CommRingCat.ofHom β) ∧
        -- semilinearity of the module maps
        (∀ (i j : Λ) (h : i ≤ j) (y : C.obj i) (x : D.obj i),
          (D.map (homOfLE h)).hom (y • x) =
            (C.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
        (∀ i (y : C.obj i) (x : D.obj i),
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
            (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i)) y •
              (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
        -- (1) the colimits
        Nonempty (IsColimit (Cocone.mk (CommRingCat.of R₁) π)) ∧
        Nonempty (IsColimit (Cocone.mk (CommRingCat.of S₁) κ)) ∧
        Nonempty (IsColimit (Cocone.mk (CommRingCat.of T₁) κ')) ∧
        Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
        -- (2) essential finite type
        (∀ i, (algebraMap ℤ (A.obj i)).EssFiniteType) ∧
        (∀ i, (ρ.app i).hom.EssFiniteType) ∧
        (∀ i, (σ.app i).hom.EssFiniteType) ∧
        -- (3) finite generation, indeed cokernels of `t × s` matrices
        (∀ i, Module.Finite (C.obj i) (D.obj i)) ∧
        (∀ i, ∃ H₀ : (Fin s → C.obj i) →ₗ[C.obj i] (Fin t → C.obj i),
          Nonempty (((Fin t → C.obj i) ⧸ LinearMap.range H₀) ≃ₗ[C.obj i] D.obj i)) ∧
        -- (4) transition base changes
        (∀ (i j : Λ) (h : i ≤ j),
          letI := (ρ.app i).hom.toAlgebra
          letI := (A.map (homOfLE h)).hom.toAlgebra
          ∃ φ : Bs.obj i ⊗[A.obj i] A.obj j →+* Bs.obj j,
            (∀ (x : Bs.obj i) (y : A.obj j),
              φ (x ⊗ₜ[A.obj i] y) = (Bs.map (homOfLE h)).hom x * (ρ.app j).hom y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] A.obj j), IsLocalization U (Bs.obj j))) ∧
        (∀ (i j : Λ) (h : i ≤ j),
          letI := (σ.app i).hom.toAlgebra
          letI := (Bs.map (homOfLE h)).hom.toAlgebra
          ∃ φ : C.obj i ⊗[Bs.obj i] Bs.obj j →+* C.obj j,
            (∀ (x : C.obj i) (y : Bs.obj j),
              φ (x ⊗ₜ[Bs.obj i] y) = (C.map (homOfLE h)).hom x * (σ.app j).hom y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] Bs.obj j), IsLocalization U (C.obj j))) ∧
        (∀ (i j : Λ) (h : i ≤ j),
          letI := (C.map (homOfLE h)).hom.toAlgebra
          ∃ e : C.obj j ⊗[C.obj i] D.obj i ≃ₗ[C.obj j] D.obj j,
            ∀ (y : C.obj j) (x : D.obj i),
              e (y ⊗ₜ[C.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
        -- (5) base changes to the limit
        (∀ i,
          letI := (ρ.app i).hom.toAlgebra
          letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R₁) (π.app i)).toAlgebra
          ∃ φ : Bs.obj i ⊗[A.obj i] R₁ →+* S₁,
            (∀ (x : Bs.obj i) (y : R₁),
              φ (x ⊗ₜ[A.obj i] y) =
                (@CommRingCat.Hom.hom _ (CommRingCat.of S₁) (κ.app i)) x * α y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] R₁), IsLocalization U S₁)) ∧
        (∀ i,
          letI := (σ.app i).hom.toAlgebra
          letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S₁) (κ.app i)).toAlgebra
          ∃ φ : C.obj i ⊗[Bs.obj i] S₁ →+* T₁,
            (∀ (x : C.obj i) (y : S₁),
              φ (x ⊗ₜ[Bs.obj i] y) =
                (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i)) x * β y) ∧
            (letI := φ.toAlgebra
             ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] S₁), IsLocalization U T₁)) ∧
        (∀ i,
          letI := (@CommRingCat.Hom.hom _ (CommRingCat.of T₁) (κ'.app i)).toAlgebra
          ∃ e : T₁ ⊗[C.obj i] D.obj i ≃ₗ[T₁] M,
            ∀ (y : T₁) (x : D.obj i),
              e (y ⊗ₜ[C.obj i] x) =
                y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)) :
    Nonempty (NoetherianLocalModelTower R S S' M) := by
  classical
  obtain ⟨Λ, po, ne, di, A, B, C, ρ, σ, π, κ, κ', D, ν, modN,
    locA, locB, locC, locρ, locσ, locAm, locBm, locCm, locπ, locκ, locκ',
    sqρ, sqσ, smulD, smulν, colA, colB, colC, colD, eftA, eftρ, eftσ,
    finD, presD, transB, transC, transD, limB, limC, limD⟩ := h
  let := po
  have := ne
  have := di
  let := modN
  have := locA
  have := locB
  have := locC
  have := locρ
  have := locσ
  have := finD
  let : ∀ i, Algebra (A.obj i) (B.obj i) := fun i ↦ (ρ.app i).hom.toAlgebra
  let : ∀ i, Algebra (B.obj i) (C.obj i) := fun i ↦ (σ.app i).hom.toAlgebra
  let : ∀ i, Algebra (A.obj i) (C.obj i) := fun i ↦
    ((σ.app i).hom.comp (ρ.app i).hom).toAlgebra
  have : ∀ i, IsScalarTower (A.obj i) (B.obj i) (C.obj i) := fun i ↦
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : ∀ i, Module (B.obj i) (D.obj i) := fun i ↦
    Module.restrictScalars (B.obj i) (C.obj i) (D.obj i)
  let : ∀ i, Module (A.obj i) (D.obj i) := fun i ↦
    Module.restrictScalars (A.obj i) (B.obj i) (D.obj i)
  have : ∀ i, IsScalarTower (B.obj i) (C.obj i) (D.obj i) := fun i ↦
    IsScalarTower.restrictScalars _ _ _
  have : ∀ i, IsScalarTower (A.obj i) (B.obj i) (D.obj i) := fun i ↦
    IsScalarTower.restrictScalars _ _ _
  let : ∀ i, Algebra (A.obj i) R := fun i ↦
    (ULift.ringEquiv.toRingHom.comp (π.app i).hom).toAlgebra
  let : ∀ i, Algebra (B.obj i) S := fun i ↦
    (ULift.ringEquiv.toRingHom.comp (κ.app i).hom).toAlgebra
  let : ∀ i, Algebra (C.obj i) S' := fun i ↦
    (ULift.ringEquiv.toRingHom.comp (κ'.app i).hom).toAlgebra
  have : ∀ i, IsNoetherianRing (A.obj i) := fun i ↦ by
    have : Algebra.EssFiniteType ℤ (A.obj i) :=
      (RingHom.essFiniteType_algebraMap).mp (eftA i)
    exact Algebra.EssFiniteType.isNoetherianRing ℤ (A.obj i)
  have : ∀ i, IsNoetherianRing (B.obj i) := fun i ↦ by
    have : Algebra.EssFiniteType (A.obj i) (B.obj i) := eftρ i
    exact Algebra.EssFiniteType.isNoetherianRing (A.obj i) (B.obj i)
  have : ∀ i, IsNoetherianRing (C.obj i) := fun i ↦ by
    have : Algebra.EssFiniteType (B.obj i) (C.obj i) := eftσ i
    exact Algebra.EssFiniteType.isNoetherianRing (B.obj i) (C.obj i)
  let liftD := AddCommGrpCat.uliftFunctor.{max u v w, t}
  have colLiftD := isColimitOfPreserves liftD colD.some
  have : PreservesFilteredColimitsOfSize.{max u v w, max u v w}
      (forget AddCommGrpCat.{max u v w t}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w t, max u v w t} _
  refine ⟨{
    ι := Λ
    R₀ := fun i ↦ A.obj i
    S₀ := fun i ↦ B.obj i
    T₀ := fun i ↦ C.obj i
    N₀ := fun i ↦ D.obj i
    rmap := fun _ _ h ↦ (A.map (homOfLE h)).hom
    smap := fun _ _ h ↦ (B.map (homOfLE h)).hom
    tmap := fun _ _ h ↦ (C.map (homOfLE h)).hom
    nmap := fun _ _ h ↦ (D.map (homOfLE h)).hom
    rmap_local := locAm
    smap_local := locBm
    tmap_local := locCm
    nmap_smul := smulD
    nlimit := fun i ↦ (ν.app i).hom
    finite := finD
    rSystem := by
      constructor
      · intro i x
        change (A.map (𝟙 i)).hom x = x
        simp
      · intro k j i hij hjk x
        change (A.map (homOfLE hij) ≫ A.map (homOfLE hjk)).hom x = _
        rw [← A.map_comp]
        rfl
    sSystem := by
      constructor
      · intro i x
        change (B.map (𝟙 i)).hom x = x
        simp
      · intro k j i hij hjk x
        change (B.map (homOfLE hij) ≫ B.map (homOfLE hjk)).hom x = _
        rw [← B.map_comp]
        rfl
    tSystem := by
      constructor
      · intro i x
        change (C.map (𝟙 i)).hom x = x
        simp
      · intro k j i hij hjk x
        change (C.map (homOfLE hij) ≫ C.map (homOfLE hjk)).hom x = _
        rw [← C.map_comp]
        rfl
    nSystem := by
      constructor
      · intro i x
        change (D.map (𝟙 i)).hom x = x
        simp
      · intro k j i hij hjk x
        change (D.map (homOfLE hij) ≫ D.map (homOfLE hjk)).hom x = _
        rw [← D.map_comp]
        rfl
    rs_comm := by
      intro i j hij
      exact congrArg CommRingCat.Hom.hom (ρ.naturality (homOfLE hij)).symm
    st_comm := by
      intro i j hij
      exact congrArg CommRingCat.Hom.hom (σ.naturality (homOfLE hij)).symm
    rlimit_local := by
      intro i
      have := locπ i
      have : IsLocalHom (ULift.ringEquiv : ULift.{max u v w} R ≃+* R).toRingHom :=
        ⟨fun a ha ↦ ha.map (ULift.ringEquiv : ULift.{max u v w} R ≃+* R).symm.toRingHom⟩
      exact RingHom.isLocalHom_comp _ _
    slimit_local := by
      intro i
      have := locκ i
      have : IsLocalHom (ULift.ringEquiv : ULift.{max u v w} S ≃+* S).toRingHom :=
        ⟨fun a ha ↦ ha.map (ULift.ringEquiv : ULift.{max u v w} S ≃+* S).symm.toRingHom⟩
      exact RingHom.isLocalHom_comp _ _
    tlimit_local := by
      intro i
      have := locκ' i
      have : IsLocalHom (ULift.ringEquiv : ULift.{max u v w} S' ≃+* S').toRingHom :=
        ⟨fun a ha ↦ ha.map (ULift.ringEquiv : ULift.{max u v w} S' ≃+* S').symm.toRingHom⟩
      exact RingHom.isLocalHom_comp _ _
    rlimit_comm := by
      intro i j hij
      ext x
      exact congrArg ULift.down
        (ConcreteCategory.congr_hom (π.naturality (homOfLE hij)) x)
    slimit_comm := by
      intro i j hij
      ext x
      exact congrArg ULift.down
        (ConcreteCategory.congr_hom (κ.naturality (homOfLE hij)) x)
    tlimit_comm := by
      intro i j hij
      ext x
      exact congrArg ULift.down
        (ConcreteCategory.congr_hom (κ'.naturality (homOfLE hij)) x)
    rs_limit_comm := by
      intro i
      ext x
      exact congrArg ULift.down (ConcreteCategory.congr_hom (sqρ i) x)
    st_limit_comm := by
      intro i
      ext x
      exact congrArg ULift.down (ConcreteCategory.congr_hom (sqσ i) x)
    nlimit_comm := by
      intro i j hij
      exact congrArg AddCommGrpCat.Hom.hom (ν.naturality (homOfLE hij))
    nlimit_smul := smulν
    rlimit_surj := by
      intro r
      obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep A colA.some (ULift.up r)
      exact ⟨i, x, congrArg ULift.down hx⟩
    slimit_surj := by
      intro r
      obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep B colB.some (ULift.up r)
      exact ⟨i, x, congrArg ULift.down hx⟩
    tlimit_surj := by
      intro r
      obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep C colC.some (ULift.up r)
      exact ⟨i, x, congrArg ULift.down hx⟩
    nlimit_surj := by
      intro m
      obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep (D ⋙ liftD) colLiftD (ULift.up m)
      exact ⟨i, x.down, congrArg ULift.down hx⟩
    rlimit_eq := by
      intro i x y hxy
      have hxy' : (π.app i) x = (π.app i) y := ULift.ext hxy
      obtain ⟨j, f, g, hfg⟩ :=
        Concrete.isColimit_exists_of_rep_eq A colA.some x y hxy'
      exact ⟨j, leOfHom f, hfg⟩
    slimit_eq := by
      intro i x y hxy
      have hxy' : (κ.app i) x = (κ.app i) y := ULift.ext hxy
      obtain ⟨j, f, g, hfg⟩ :=
        Concrete.isColimit_exists_of_rep_eq B colB.some x y hxy'
      exact ⟨j, leOfHom f, hfg⟩
    tlimit_eq := by
      intro i x y hxy
      have hxy' : (κ'.app i) x = (κ'.app i) y := ULift.ext hxy
      obtain ⟨j, f, g, hfg⟩ :=
        Concrete.isColimit_exists_of_rep_eq C colC.some x y hxy'
      exact ⟨j, leOfHom f, hfg⟩
    nlimit_eq := by
      intro i x y hxy
      have hxy' : (liftD.map (ν.app i)) (ULift.up x) =
          (liftD.map (ν.app i)) (ULift.up y) := ULift.ext hxy
      obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq
        (D ⋙ liftD) colLiftD (ULift.up x) (ULift.up y) hxy'
      exact ⟨j, leOfHom f, congrArg ULift.down hfg⟩
    baseTransition := by
      intro i j hij
      exact tensorLocalization_tower_transition (A.obj i) (B.obj i) (C.obj i)
        (A.obj j) (B.obj j) (C.obj j) (A.map (homOfLE hij)).hom
        (B.map (homOfLE hij)).hom (C.map (homOfLE hij)).hom
        (transB i j hij) (transC i j hij)
    fibreTransition := by
      intro i j hij
      obtain ⟨f, hf, U, hU⟩ := transC i j hij
      exact ⟨f, U, hf, hU⟩
    moduleTransition := transD
    baseLocalization := by
      intro i
      obtain ⟨φ, hφ, U, hU⟩ := limB i
      let e : B.obj i ⊗[A.obj i] ULift.{max u v w} R ≃+* R ⊗[A.obj i] B.obj i :=
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : B.obj i ≃ₐ[A.obj i] B.obj i)
          (ULift.algEquiv : ULift.{max u v w} R ≃ₐ[A.obj i] R)).trans
          (Algebra.TensorProduct.comm (A.obj i) (B.obj i) R)).toRingEquiv
      let ψ : R ⊗[A.obj i] B.obj i →+* S :=
        ULift.ringEquiv.toRingHom.comp (φ.comp e.symm.toRingHom)
      let : Algebra (R ⊗[A.obj i] B.obj i) S := ψ.toAlgebra
      have hloc : IsLocalization (U.map e) S := by
        let : Algebra (B.obj i ⊗[A.obj i] ULift.{max u v w} R)
            (ULift.{max u v w} S) := φ.toAlgebra
        have : IsLocalization U (ULift.{max u v w} S) := hU
        let : Algebra (R ⊗[A.obj i] B.obj i) (ULift.{max u v w} S) :=
          (φ.comp e.symm.toRingHom).toAlgebra
        have hloc' := IsLocalization.isLocalization_of_base_ringEquiv
          U (ULift.{max u v w} S) e
        exact (IsLocalization.isLocalization_iff_of_ringEquiv
          (U.map e) (ULift.ringEquiv : ULift.{max u v w} S ≃+* S)).mp hloc'
      have : IsScalarTower R (R ⊗[A.obj i] B.obj i) S := by
        apply IsScalarTower.of_algebraMap_eq
        intro r
        change algebraMap R S r = ψ (r ⊗ₜ[A.obj i] 1)
        dsimp [ψ, e]
        rw [hφ, map_one, one_mul]
        simp only [RingHom.ulift_apply]
        rfl
      exact ⟨U.map e, ⟨(IsLocalizedModule.iso (U.map e)
        (Algebra.linearMap (R ⊗[A.obj i] B.obj i) S)).restrictScalars R⟩⟩
    moduleLocalization := by
      intro i
      obtain ⟨φ, hφ, hloc⟩ := limC i
      obtain ⟨e, he⟩ := limD i
      exact localizedModule_of_liftedTensorComparison S S' (B.obj i) (C.obj i)
        (D.obj i) M (κ'.app i).hom φ (by intro c; simpa using hφ c 1)
        (by intro s; simpa only [map_one, one_mul, RingHom.ulift_apply] using
          hφ 1 (ULift.up s)) hloc ⟨e⟩ }⟩

end Module
