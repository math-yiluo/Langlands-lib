/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Continuous cohomology under coefficient equivalences across universes

Source: Stacks Project, Etale Cohomology, Section 0DVG, cochain construction.
(blueprint: lem-sc-continuous-cohomology-coefficient-equiv).
-/

@[expose] public section

universe u s t

namespace Rep

open CategoryTheory

private def coindEquiv {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : TopRep.{max u s} R G} {N : TopRep.{max u t} R G}
    (e : M.ρ.Equiv N.ρ) : M.coind₁.ρ.Equiv N.coind₁.ρ :=
  ContRepresentation.Equiv.mk
    { toFun := ContRepresentation.coind₁Map e.toContIntertwiningMap
      invFun := ContRepresentation.coind₁Map e.symm.toContIntertwiningMap
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := fun f ↦ by ext g; exact e.symm_apply_apply (f g)
      right_inv := fun f ↦ by ext g; exact e.apply_symm_apply (f g)
      continuous_toFun := (ContRepresentation.coind₁Map e.toContIntertwiningMap).cont
      continuous_invFun :=
        (ContRepresentation.coind₁Map e.symm.toContIntertwiningMap).cont }
    (ContRepresentation.coind₁Map e.toContIntertwiningMap).isIntertwining'

private def resolutionEquiv {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : TopRep.{max u s} R G} {N : TopRep.{max u t} R G}
    (e : M.ρ.Equiv N.ρ) :
    (n : ℕ) → (TopRep.resolutionX M n).ρ.Equiv (TopRep.resolutionX N n).ρ
  | 0 => e
  | n + 1 => coindEquiv (resolutionEquiv e n)

private theorem resolutionEquiv_d {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : TopRep.{max u s} R G} {N : TopRep.{max u t} R G}
    (e : M.ρ.Equiv N.ρ) (n : ℕ) (x : (TopRep.resolutionX M n).V) :
    resolutionEquiv e (n + 1) ((TopRep.d M n).hom x) =
      (TopRep.d N n).hom (resolutionEquiv e n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply ContinuousMap.ext
    intro g
    change resolutionEquiv e (n + 1)
        (x - (TopRep.d M n).hom (x g)) =
      resolutionEquiv e (n + 1) x -
        (TopRep.d N n).hom (resolutionEquiv e n (x g))
    rw [map_sub, ih]

private def invariantsEquiv {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : TopRep.{max u s} R G} {N : TopRep.{max u t} R G}
    (e : M.ρ.Equiv N.ρ) : M.ρ.invariants ≃ₗ[R] N.ρ.invariants where
  toFun := e.toContIntertwiningMap.mapInvariants
  invFun := e.symm.toContIntertwiningMap.mapInvariants
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' := map_add _
  map_smul' := map_smul _

private def cochainsEquiv {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : TopRep.{max u s} R G} {N : TopRep.{max u t} R G}
    (e : M.ρ.Equiv N.ρ) (n : ℕ) :
    (TopRep.homogeneousCochains M).X n ≃ₗ[R] (TopRep.homogeneousCochains N).X n :=
  invariantsEquiv (resolutionEquiv e (n + 1))

private theorem cochainsEquiv_d {R : Type*} [CommRing R] [TopologicalSpace R]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : TopRep.{max u s} R G} {N : TopRep.{max u t} R G}
    (e : M.ρ.Equiv N.ρ) (i j : ℕ) (x : (TopRep.homogeneousCochains M).X i) :
    cochainsEquiv e j (((TopRep.homogeneousCochains M).d i j).hom x) =
      ((TopRep.homogeneousCochains N).d i j).hom (cochainsEquiv e i x) := by
  by_cases h : i + 1 = j
  · subst j
    apply Subtype.ext
    change resolutionEquiv e (i + 1 + 1)
        (((TopRep.homogeneousCochains M).d i (i + 1)).hom x).val =
      (((TopRep.homogeneousCochains N).d i (i + 1)).hom (cochainsEquiv e i x)).val
    rw [TopRep.homogeneousCochains.d_apply, TopRep.homogeneousCochains.d_apply]
    exact resolutionEquiv_d e (i + 1) x.val
  · have h' : ¬(ComplexShape.up ℕ).Rel i j := h
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    rw [TopModuleCat.hom_zero_apply, TopModuleCat.hom_zero_apply, map_zero]

private noncomputable def concreteData {R : Type*} [Ring R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat.{s} R)) : S.LeftHomologyData :=
  ⟨_, _, _, _, _, TopModuleCat.isLimitKer S.g, by simp, TopModuleCat.isColimitCoker _⟩

private noncomputable def shortComplexEquiv {R : Type*} [CommRing R] [TopologicalSpace R]
    (S : ShortComplex (TopModuleCat.{s} R)) (T : ShortComplex (TopModuleCat.{t} R))
    (e₁ : S.X₁ ≃ₗ[R] T.X₁) (e₂ : S.X₂ ≃ₗ[R] T.X₂) (e₃ : S.X₃ ≃ₗ[R] T.X₃)
    (hf : ∀ x, e₂ (S.f.hom x) = T.f.hom (e₁ x))
    (hg : ∀ x, e₃ (S.g.hom x) = T.g.hom (e₂ x)) :
    S.homology ≃ₗ[R] T.homology := by
  let k : S.g.hom.ker ≃ₗ[R] T.g.hom.ker :=
    { toFun := fun x ↦ ⟨e₂ x, by
        change T.g.hom (e₂ x.val) = 0
        have hx : S.g.hom x.val = 0 := x.property
        rw [← hg, hx, map_zero]⟩
      invFun := fun x ↦ ⟨e₂.symm x, by
        change S.g.hom (e₂.symm x.val) = 0
        apply e₃.injective
        have hx : T.g.hom x.val = 0 := x.property
        rw [hg, e₂.apply_symm_apply, hx, map_zero]⟩
      left_inv := fun x ↦ Subtype.ext (e₂.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e₂.apply_symm_apply x)
      map_add' := fun x y ↦ Subtype.ext (map_add e₂ x.val y.val)
      map_smul' := fun r x ↦ Subtype.ext (map_smul e₂ r x.val) }
  let DS := concreteData S
  let DT := concreteData T
  have hDS (z : S.X₁) : (DS.f'.hom z).val = S.f.hom z := by
    exact ConcreteCategory.congr_hom DS.f'_i z
  have hDT (z : T.X₁) : (DT.f'.hom z).val = T.f.hom z := by
    exact ConcreteCategory.congr_hom DT.f'_i z
  have hmap : DS.f'.hom.range.map k.toLinearMap = DT.f'.hom.range := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      refine ⟨e₁ z, ?_⟩
      apply Subtype.ext
      change (DT.f'.hom (e₁ z)).val = e₂ (DS.f'.hom z).val
      rw [hDT, hDS, hf]
    · rintro ⟨z, rfl⟩
      refine ⟨DS.f'.hom (e₁.symm z), ⟨e₁.symm z, rfl⟩, ?_⟩
      apply Subtype.ext
      change e₂ (DS.f'.hom (e₁.symm z)).val = (DT.f'.hom z).val
      rw [hDS, hDT, hf, e₁.apply_symm_apply]
  let q := Submodule.Quotient.equiv DS.f'.hom.range DT.f'.hom.range k hmap
  exact ((forget₂ _ (ModuleCat R)).mapIso DS.homologyIso).toLinearEquiv ≪≫ₗ q ≪≫ₗ
    ((forget₂ _ (ModuleCat R)).mapIso DT.homologyIso).toLinearEquiv.symm

/-- Equivariant linear equivalences of discrete coefficients induce additive equivalences
of continuous cohomology, including between different coefficient universes.

Source: Stacks Project, Etale Cohomology, Section 0DVG, cochain construction.
(blueprint: lem-sc-continuous-cohomology-coefficient-equiv).

Proof: The equivalence e and its inverse are continuous because the coefficient spaces
are discrete. Postcompose each homogeneous cochain with e, recursively through its
iterated continuous maps; the compact-open topology makes these postcomposition maps
continuous. Equivariance of e preserves the invariant submodules. Its inverse is
equivariant as well, by applying e to the required equality and using injectivity.
The recursive differential is constant insertion minus postcomposition with the preceding
differential. Postcomposition commutes with constants and subtraction, so these degreewise
linear equivalences commute with every differential. Thus they restrict to inverse
bijections on cocycles and carry coboundaries onto coboundaries. On the quotient of
cocycles by coboundaries they give inverse equivalences. Underlying TopModuleCat homology
is precisely this algebraic quotient, as its kernels and cokernels are module kernels
and quotients endowed with subspace and quotient topologies. This construction is
performed on types and their subquotients and therefore allows different universes. -/
@[no_expose]
noncomputable def continuousCohomologyAddEquivOfCoefficients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TopRep.{max u s} ℤ G) (N : TopRep.{max u t} ℤ G)
    [DiscreteTopology M.V] [DiscreteTopology N.V]
    (e : M.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : M.V), e (M.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    continuousCohomology q M ≃+ continuousCohomology q N := by
  let : Module ℤ M.V := M.hV2
  let : Module ℤ N.V := N.hV2
  let a : M.ρ.Equiv N.ρ := ContRepresentation.Equiv.mk (ρ := M.ρ) (σ := N.ρ)
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := fun r x ↦ by
        change e (M.hV2.smul r x) = N.hV2.smul r (e x)
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
        exact map_zsmul e r x
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
    (fun g ↦ by ext x; exact he g x)
  exact (shortComplexEquiv
    ((TopRep.homogeneousCochains M).sc q) ((TopRep.homogeneousCochains N).sc q)
    (cochainsEquiv a ((ComplexShape.up ℕ).prev q)) (cochainsEquiv a q)
    (cochainsEquiv a ((ComplexShape.up ℕ).next q))
    (cochainsEquiv_d a _ _) (cochainsEquiv_d a _ _)).toAddEquiv

end Rep
