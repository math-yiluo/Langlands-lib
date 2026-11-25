/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.MarkedFiniteFreeLiftCompatibility
import WeilConjectures.RingTheory.UnmarkedFiniteFreeLift

/-!
# Lifting a marked finite free complex across a nilpotent quotient

Source: Stacks Project, More on Algebra, Tags 0H76, 0BCB, and the choice of delta in
Tag 0BCA (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory

namespace DerivedCategory

/-- A prescribed bounded-above finite-free model of derived reduction lifts with its marking
and its upper bound. `L` and `ε` express derived scalar extension by its universal property,
as in derived change of rings on the one-object site. The right side of the final equality
first applies the canonical counit comparison from derived to termwise reduction, then
`Q(θ)`. Thus it says exactly `Q(θ) = α ∘ (β ⊗ᴸ R/I)` under that comparison.
Source: Stacks Project, More on Algebra, Tags 0H76, 0BCB, and 0BCA
(auxiliary; not a blueprint node).

Proof:
1. Choose a bounded-above finite-free representative L₀ of K by pseudo-coherence. It is
   K-flat by lem-pc-module-bounded-flat-kflat. Use lem-pur-derived-change-of-rings to
   compute reduction termwise, and lem-pc-ring-derived-map-representative to represent
   the inverse of the prescribed marking by a quasi-isomorphism δ : F → L₀/IL₀.
2. Use all projective modules as the lifting class (def-weil-pbc-projective-module).
   Sums and summands stay projective. If M/IM = 0, then M = IM = I^N M = 0, so
   surjectivity is reflected by reduction. Each finite free term of F lifts to a free
   module. By lem-sc-complex-lift-cone-properties, Cone(δ) is bounded above and acyclic.
3. Apply lem-sc-complex-lift-acyclic-projective to lift this cone to an acyclic bounded
   above projective complex A with an identification e of its reduction with Cone(δ).
4. By lem-sc-complex-lift-strict-map lift the cone inclusion to f : L₀ → A.
   By lem-sc-complex-lift-cone-cokernel its cokernel B reduces to F[1], by second-coordinate
   projection ρ. Apply lem-sc-projective-class-reduced-splitting degreewise to see that
   f is split injective and B is projective. Put P = B[-1] and θ = ρ[-1].
5. Lift a finite basis of each F term to P. Its span has cokernel T with T/IT = 0,
   so nilpotence kills T and P is finite. By lem-sc-finite-projective-free-mod-ideal,
   projectivity and the one-plus-ideal unit hypothesis make P free. Zero terms of F
   force zero terms of P by the same nilpotent argument, retaining the bound b.
6. For D = Cone(f), the projection -p : D → L₀[1] is a quasi-isomorphism since A is
   acyclic (lem-sf-derived-homology-long-exact). The map t : D → B is a quasi-isomorphism:
   its kernel has pairs (x,l) with differential (dx+l,-dl) and contraction (x,l) ↦ (0,x).
   Set β = γ ∘ Q((-p)[-1]) ∘ Q(t[-1])⁻¹, where γ identifies Q(L₀) with K.
7. All complexes used are bounded above and projective, hence flat and K-flat. Derived
   change of rings therefore computes their reduction by these chain maps. In the
   coordinates (x,y,z) on the reduced D the differential is (dx+δy+z,-dy,-dz).
   The degree-minus-one map h(x,y,z)=x satisfies dh+hd = δ[1]ρt+p. Consequently
   Q(-p) = Q(δ[1])Q(ρt). Shift back and cancel Q(t[-1]); since α Q(γ reduced) Q(δ)=1,
   this gives the stated marking equality, including its sign. -/
theorem exists_marked_finiteFree_lift_of_nilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hnil : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = 0)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} (R ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (F : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (b : ℤ) (hFbound : F.IsStrictlyLE b)
    (hFterms : ∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i))
    (α : L.obj K ≅ Q.obj F) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β : Q.obj P ≅ K)
      (θ : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      L.map β.hom ≫ α.hom =
        L.map ((quotientCompQhIso (ModuleCat.{max u v} R)).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        Qh.map ((@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ _
          (ModuleCat.extendScalars (Ideal.Quotient.mk I))
          (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
          (.up ℤ)).hom.app P) ≫
        (quotientCompQhIso (ModuleCat.{max u v} (R ⧸ I))).hom.app _ ≫
        Q.map θ.hom := by
  obtain ⟨P, β, θ, hbound, hfree⟩ :=
    exists_unmarked_finiteFree_lift_of_nilpotent I hnil hunits L ε K hK F b hFbound hFterms α
  exact exists_marking_compatible_finiteFree_lift I hnil hunits L ε K hK F b hFbound hFterms α
    ⟨P, β, θ, hbound, hfree⟩

end DerivedCategory
