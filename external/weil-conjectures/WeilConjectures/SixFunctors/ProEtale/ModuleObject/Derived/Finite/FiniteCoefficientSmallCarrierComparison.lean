/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap

/-!
# Finite coefficients and small continuous-function carriers

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/_section.md, coefficient list (1)--(3), and the encoding bridge
in proof steps 1--6 of the DAG node.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison).

The two endpoints are the actual `cartesianFinitePointRing` and
`Profinite.continuousMapRingObj`. The comparison postcomposes by a ring equivalence;
canonical universe lifts let the recorded postcomposition API handle both endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Opposite
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bundle the actual finite-coefficient sheaf, with its fixed bottom topology and
canonical commutative ring-object structure. This introduces no new coefficient model.
Source: CartesianCoefficients.lean, `cartesianFinitePointRing`, and node statement D_u(A).
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
abbrev finiteCoefficientComparisonSource (A : Type u) [CommRing A] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  exact CommMon.mk (cartesianFinitePointRing A)

/-- Bundle the recorded continuous-function sheaf and its canonical commutative structure.
Source: ContinuousMapCondensedRing.lean and node statement C_u(T).
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
abbrev finiteCoefficientComparisonTarget (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) :=
  CommMon.mk (Profinite.continuousMapRingObj T)

/-- Postcompose finite-coefficient sections by the carrier ring equivalence.
The existing universe-polymorphic postcomposition first lands in `ULift T`; lowering
that auxiliary carrier gives sections in the actual small-carrier endpoint. The
forgetful `sheafCompose` and its `IsMonHom` instance retain multiplication and unit.
Source: node proof step 3, using def-sfb-continuous-map-condensed-ring-map.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
def finiteCoefficientComparisonHom (A : Type u) [CommRing A]
    (T : Type) [CommRing T] [TopologicalSpace T] [DiscreteTopology T] (r : A ≃+* T) :
    finiteCoefficientComparisonSource A ⟶ finiteCoefficientComparisonTarget T := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  let rUp : A →+* ULift.{u} T := ULift.ringEquiv.symm.toRingHom.comp r.toRingHom
  let k := Profinite.continuousMapRingSheafMapOfUniverse.{u, u} rUp
    continuous_of_discreteTopology
  let g : Profinite.continuousCoefficientRingSheaf A ⟶
      Profinite.continuousMapRingSheaf T :=
    ⟨{ app := fun S ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((ULift.ringEquiv.toRingHom.compLeftContinuous _ continuous_uliftDown).comp
            (ULift.ringEquiv.toRingHom.comp (k.hom.app S).hom)))
       naturality := fun _ _ _ ↦ rfl }⟩
  let m : cartesianFinitePointRing A ⟶ Profinite.continuousMapRingObj T :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map g
  letI : IsMonHom m := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) g
  exact CommMon.homMk (Mon.Hom.mk m)

/-- Postcompose small-carrier sections by the inverse carrier ring equivalence.
Lift the auxiliary coefficient carrier before applying the recorded postcomposition
map, then forget to abelian sheaves with its canonical `IsMonHom` compatibility.
Source: node proof step 3, using def-sfb-continuous-map-condensed-ring-map.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
def finiteCoefficientComparisonInv (A : Type u) [CommRing A]
    (T : Type) [CommRing T] [TopologicalSpace T] [DiscreteTopology T] (r : A ≃+* T) :
    finiteCoefficientComparisonTarget T ⟶ finiteCoefficientComparisonSource A := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  let rDown : ULift.{u} T →+* A := r.symm.toRingHom.comp ULift.ringEquiv.toRingHom
  let k := Profinite.continuousMapRingSheafMapOfUniverse.{u, u} rDown
    continuous_of_discreteTopology
  let g : Profinite.continuousMapRingSheaf T ⟶
      Profinite.continuousCoefficientRingSheaf A :=
    ⟨{ app := fun S ↦ RingCat.ofHom ((k.hom.app S).hom.comp
          (ULift.ringEquiv.symm.toRingHom.comp
            (((ULift.ringEquiv : ULift.{u} T ≃+* T).symm.toRingHom.compLeftContinuous _
              continuous_uliftUp).comp
              ULift.ringEquiv.toRingHom)))
       naturality := fun _ _ _ ↦ rfl }⟩
  let m : Profinite.continuousMapRingObj T ⟶ cartesianFinitePointRing A :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map g
  letI : IsMonHom m := Sheaf.isMonHom_sheafCompose_map
    (coherentTopology Profinite.{u}) g
  exact CommMon.homMk (Mon.Hom.mk m)

/-- The forward and inverse postcomposition maps compose to the identity on D_u(A).
Source: node proof step 4. On a section s, the composite has value
r.symm (r (s x)) = s x. Extensionality of functions, continuous maps, lifted sections,
sheaf maps and bundled ring-object maps proves the identity, including empty S.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
theorem finiteCoefficientComparison_hom_inv_id (A : Type u) [CommRing A]
    (A₀ : Type) [CommRing A₀] [TopologicalSpace A₀] [DiscreteTopology A₀]
    (r : A ≃+* A₀) :
    finiteCoefficientComparisonHom A A₀ r ≫ finiteCoefficientComparisonInv A A₀ r = 𝟙 _ := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  ext S s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change r.symm (r (s.down x)) = s.down x
  exact r.symm_apply_apply _

/-- The inverse and forward postcomposition maps compose to the identity on C_u(A₀).
Source: node proof step 4. On a section t, the composite has value
r (r.symm (t x)) = t x. The same sectionwise and bundled-map extensionality proves
this identity. No nonzero-ring hypothesis is used.
(blueprint: lem-sfb-finite-coefficient-small-carrier-comparison). -/
theorem finiteCoefficientComparison_inv_hom_id (A : Type u) [CommRing A]
    (A₀ : Type) [CommRing A₀] [TopologicalSpace A₀] [DiscreteTopology A₀]
    (r : A ≃+* A₀) :
    finiteCoefficientComparisonInv A A₀ r ≫ finiteCoefficientComparisonHom A A₀ r = 𝟙 _ := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  ext S s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change r (r.symm (s.down x)) = s.down x
  exact r.apply_symm_apply _

end AlgebraicGeometry.ProEtale.CondensedRing
