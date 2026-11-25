/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites

/-! # Finite-free coefficient restriction on entire derived systems

Source: finite-free coefficient tensor in the blueprint coefficient comparison;
Stacks 07A6, 03DI, 03DJ and 0F7B--0F7F
(blueprint: lem-coef-finite-free-system-restriction).

Natural transformations below live on the ordinary unbounded derived categories
of strict semilinear systems, before evaluation and inverse limit.
The data are recorded by (blueprint: def-coef-finite-free-system-data).
Index n means positive exponent n+1. The upper coefficients are S/pi^(n+1)S,
including ramification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
open WeilConjectures.SemilinearSections
namespace WeilConjectures.FiniteFreeSystemRestriction

universe v w

/-- Quotient by the indicated uniformizer power, with its actual exponent.
Source: the coefficient quotient in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev quotient (R : Type (u + 1)) [CommRing R] (pi : R) (n : ℕ) :=
  R ⧸ (Ideal.span {pi}) ^ (n + 1)

/-- The quotient transition is induced by the identity of the integer ring.
Source: the coefficient quotient in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def quotientTransition (R : Type (u + 1)) [CommRing R] (pi : R) (n : ℕ) :
    quotient R pi (n + 1) →+* quotient R pi n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- Inclusion followed by quotient, with the source uniformizer on both sides.
Source: the compatible coefficient inclusion in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def quotientMap {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (pi : R) (n : ℕ) :
    quotient R pi n →+* quotient S (f pi) n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp f) (by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    simpa only [map_pow] using map_dvd f hx)

variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

/-- Lower coefficient ring at positive exponent n+1.
Source: the A tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev A (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))

/-- Upper coefficient ring, using the image of the lower uniformizer.
Source: the B tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev B (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (quotient (Padic.coefficientExtensionIntegers l L)
    (integralScalarIntegerInclusion l E L i (Padic.coefficientExtensionUniformizer l E)) n)

/-- Actual lower quotient transitions.
Source: the A tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev aTransition (n : ℕ) : A l E (n + 1) ⟶ A l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1))

/-- Actual upper quotient transitions, retaining all ramified levels en.
Source: the B tower in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev bTransition (n : ℕ) : B l E L i (n + 1) ⟶ B l E L i n :=
  CommRingCat.ofHom (quotientTransition _ _ n)

/-- The specified compatible inclusion at each positive coefficient level.
Source: the A-to-B map in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev levelMap (n : ℕ) : A l E n ⟶ B l E L i n :=
  CommRingCat.ofHom (quotientMap (integralScalarIntegerInclusion l E L i)
    (Padic.coefficientExtensionUniformizer l E) n)


/-- The specified level maps commute with the actual quotient transitions.
Source: coefficient inclusion in the node
(blueprint: lem-coef-finite-free-system-restriction).
Proof: quotient induction reduces both composites to x mapped to the residue of i(x).
Ring-homomorphism extensionality then gives their equality. -/
theorem levelMap_transition (n : ℕ) :
    levelMap l E L i (n + 1) ≫ bTransition l E L i n =
      aTransition l E n ≫ levelMap l E L i n := by
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

/-- The level map on constant ring sheaves.
Source: sectionwise coefficient inclusion in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev sheafMap (X : Scheme.{u}) (n : ℕ) :
    coefficients (A l E) X n ⟶ coefficients (B l E L i) X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (levelMap l E L i n)

/-- The coefficient map on the single ringed sequence site, retaining all transitions.
Source: proof Step 1 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def systemInclusion (X : Scheme.{u}) :
    ringSystem (A l E) (aTransition l E) X ⟶
      ringSystem (B l E L i) (bTransition l E L i) X :=
  systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients (A l E) X) (transition (A l E) (aTransition l E) X)
    (coefficients (B l E L i) X) (transition (B l E L i) (bTransition l E L i) X)
    (sheafMap l E L i X) (fun n ↦ by
      simpa only [sheafMap, AlgebraicGeometry.ProEtale.SemilinearProperOpen.transition,
        ← Functor.map_comp] using
        congrArg ((constantSheaf.{u, u + 1, u + 1, u + 2}
          (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map)
          (levelMap_transition l E L i n))

/-- Ordinary termwise restriction along the actual coefficient-system map.
Source: proof Step 1 of the node, using the dependency's restriction functor
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev U0 (X : Scheme.{u}) := res.{u + 1, u, u + 1} (systemInclusion l E L i X)

/-- Derived restriction, computed by termwise localization.
Source: proof Step 5 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
@[reducible] def U (X : Scheme.{u}) :
    Derived (B l E L i) (bTransition l E L i) X ⥤
      Derived (A l E) (aTransition l E) X :=
  resD.{u + 1, u, u + 1} (systemInclusion l E L i X)

/-- The upper coefficient system considered as an ordinary lower-coefficient system.
Source: the coefficient system B in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev coefficientModule (X : Scheme.{u}) :=
  (U0 l E L i X).obj (SheafOfModules.unit
    (ring.{u + 1, u, u + 1} (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology X))
      (ringSystem (B l E L i) (bTransition l E L i) X)))

/-- The upper coefficient system in degree zero, with the restricted action.
Source: the normalized coefficient system in the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev coefficientObject (X : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (Modules (A l E) (aTransition l E) X) 0).obj
    (coefficientModule l E L i X)

/-- The finite-type separated k-schemes occurring in this statement, using the
standard bundled category of schemes over the field and the existing properties.
Source: geometric hypotheses of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
abbrev Spaces (D : FiniteFieldDatum.{u}) :=
  { X : Over (Spec (CommRingCat.of D.k)) //
    IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom }

/-- The section-normalized ordinary inverse-image/direct-image scalar square.
Source: proof Step 6 of the node; the mate equation includes both geometric
adjunction unit and counit compatibilities
(blueprint: lem-coef-finite-free-system-restriction). -/
structure OrdinarySquare {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The direct-image comparison is identity on the same section groups. -/
  push : AlgebraicGeometry.ProEtale.SemilinearProperOpen.push
      (B l E L i) (bTransition l E L i) f ⋙ U0 l E L i Y ≅
    U0 l E L i X ⋙ AlgebraicGeometry.ProEtale.SemilinearProperOpen.push
      (A l E) (aTransition l E) f
  /-- Identity on sections, simultaneously in the level and site directions. -/
  push_section : ∀ (M : Modules (B l E L i) (bTransition l E L i) X)
    (V : (ℕ × Y.ProEt)ᵒᵖ),
    HEq (fun x ↦ (push.hom.app M).val.app V x)
      (fun x : ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.push
        (B l E L i) (bTransition l E L i) f).obj M).val.obj V ↦ x)
  /-- Pullback is the inverse adjunct of the sectionwise comparison. -/
  pull : AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull
      (B l E L i) (bTransition l E L i) f ⋙ U0 l E L i X ≅
    U0 l E L i Y ⋙ AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull
      (A l E) (aTransition l E) f
  /-- The ordinary comparison respects the specified adjunctions. -/
  mate : (mateEquiv (ordinaryAdj (B l E L i) (bTransition l E L i) f)
    (ordinaryAdj (A l E) (aTransition l E) f)
      (TwoSquare.mk _ _ _ _ pull.inv)) = push.hom

/-- The exact pullback comparison on entire derived systems.
Source: proof Step 8 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def OrdinarySquare.derivedPull {X Y : Scheme.{u}} {f : X ⟶ Y}
    (q : OrdinarySquare l E L i f) :
    P (B l E L i) (bTransition l E L i) f ⋙ U l E L i X ≅
      U l E L i Y ⋙ P (A l E) (aTransition l E) f :=
  Functor.mapDerivedCategorySquareIso q.pull

/-- The derived pushforward comparison is the specified geometric right mate.
Source: proof Step 8 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def OrdinarySquare.derivedPush {X Y : Scheme.{u}} {f : X ⟶ Y}
    (q : OrdinarySquare l E L i f) :
    R (B l E L i) (bTransition l E L i) f ⋙ U l E L i Y ⟶
      U l E L i X ⋙ R (A l E) (aTransition l E) f :=
  (mateEquiv (adj (B l E L i) (bTransition l E L i) f)
    (adj (A l E) (aTransition l E) f)
      (TwoSquare.mk _ _ _ _ (q.derivedPull l E L i).inv))

/-- The inverse open-extension comparison is the specified open-adjunction mate.
Its invertibility is asserted separately, never inferred merely from a mate formula.
Source: proof Step 9 of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def OrdinarySquare.derivedOpenInv {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsOpenImmersion f] (q : OrdinarySquare l E L i f) :
    U l E L i X ⋙ J (A l E) (aTransition l E) f ⟶
      J (B l E L i) (bTransition l E L i) f ⋙ U l E L i Y :=
  ((mateEquiv (jAdj (B l E L i) (bTransition l E L i) f)
    (jAdj (A l E) (aTransition l E) f)).symm
      (TwoSquare.mk _ _ _ _ (q.derivedPull l E L i).hom))

/-- The simultaneous geometric comparisons on the specified finite-type k-schemes.
Source: geometric comparison clauses of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
structure Geometry (D : FiniteFieldDatum.{u}) where
  /-- The comparisons already exist on the abelian system categories. -/
  ordinary : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    OrdinarySquare l E L i f
  /-- The derived geometric right mate is invertible. -/
  push_isIso : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    IsIso ((ordinary X Y f).derivedPush l E L i)
  /-- The derived open-adjunction mate is invertible. -/
  open_isIso : ∀ (X Y : Spaces D) (j : X.val.left ⟶ Y.val.left)
    [IsOpenImmersion j], IsIso ((ordinary X Y j).derivedOpenInv l E L i)
  /-- Constant coefficient sections give the actual ordinary pushforward map. -/
  coefficient_push : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    coefficientModule l E L i Y.val.left ⟶
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.push (A l E) (aTransition l E) f).obj
        (coefficientModule l E L i X.val.left)
  /-- Its sections are exactly the structural constant-section map for B. -/
  coefficient_push_section : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left)
    (V : (ℕ × Y.val.left.ProEt)ᵒᵖ),
    HEq (fun x ↦ (coefficient_push X Y f).val.app V x)
      (fun x ↦ (coefficientMap (B l E L i) (bTransition l E L i) f).hom.app V x)
  /-- Its ordinary pullback adjunct is invertible; exact localization gives the
  coefficient pullback isomorphism with precisely this constant-section normalization. -/
  coefficient_pull_isIso : ∀ (X Y : Spaces D) (f : X.val.left ⟶ Y.val.left),
    IsIso (((ordinaryAdj (A l E) (aTransition l E) f).homEquiv _ _).symm
      (coefficient_push X Y f))

/-- The strict-system realization of a fixed compactification h = pj.
Source: the compact-support clause of the node
(blueprint: lem-coef-finite-free-system-restriction). -/
def compact (C : ℕ → CommRingCat.{u + 1}) (t : ∀ n, C (n + 1) ⟶ C n)
    {X W Y : Scheme.{u}} (j : X ⟶ W) (p : W ⟶ Y) [IsOpenImmersion j] :=
  J C t j ⋙ R C t p

end WeilConjectures.FiniteFreeSystemRestriction
