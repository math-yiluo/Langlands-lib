/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExact
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemVerdier
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.LinearAlgebra.Dimension.Free

import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import WeilConjectures.CategoryTheory.StageSystem.Shift
import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionAssociatorShifts
import Mathlib.Algebra.Group.Ext

/-! # Algebraically closed coefficients without idempotent completion

Source: blueprint `sec-smooth-purity/sk-def-sf-operations`, order 1462
(blueprint: def-weil-algebraically-closed-coefficients).
Objects are actual pairs and Hom is the directed colimit of the stated abelian groups.
The existing upstream pair category supplies its quotient, identities and composition;
its Hom groups are canonically the displayed abelian-group colimits.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe d u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures

section
attribute [local irreducible] rationalTriangulationDatum rationalConstructibleScalarComp

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
  (Y : AlgebraicGeometry.Scheme.{u})
/-- Transport the tensor associator along equality of the coefficient map itself.
Source: normalized tensor composition
(blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def correctedTensorAssociator
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M)
    (ij : E →ₐ[Padic l] M) (hij : j.comp i = ij) :
    rationalScalarExtension D l hl E Y L i ⋙ rationalScalarExtension D l hl L Y M j ≅
      rationalScalarExtension D l hl E Y M ij := by
  subst ij
  exact rationalConstructibleScalarComp l E L i Y M j D hl

/-- Direct transport agrees with composing the tensor iso and its equality iso.
Source: equality induction (blueprint: def-weil-algebraically-closed-coefficients). -/
theorem correctedTensorAssociator_formula
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M)
    (ij : E →ₐ[Padic l] M) (hij : j.comp i = ij) :
    correctedTensorAssociator D l hl E L M Y i j ij hij =
      rationalConstructibleScalarComp l E L i Y M j D hl ≪≫
        eqToIso (congrArg (rationalScalarExtension D l hl E Y M) hij) := by
  subst ij
  simp only [correctedTensorAssociator, eqToIso_refl, Iso.trans_refl]

private theorem pentagon (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M)
    (k : M →ₐ[Padic l] N) (ij : E →ₐ[Padic l] M) (jk : L →ₐ[Padic l] N)
    (ijk : E →ₐ[Padic l] N) (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hijk : k.comp ij = ijk) (hijk' : jk.comp i = ijk)
    (K : rationalConstructibleCategory D l hl E Y) :
    (rationalScalarExtension D l hl M Y N k).map
        ((correctedTensorAssociator D l hl E L M Y i j ij hij).hom.app K) ≫
        (correctedTensorAssociator D l hl E M N Y ij k ijk hijk).hom.app K =
      (correctedTensorAssociator D l hl L M N Y j k jk hjk).hom.app
          ((rationalScalarExtension D l hl E Y L i).obj K) ≫
        (correctedTensorAssociator D l hl E L N Y i jk ijk hijk').hom.app K := by
  subst ij
  subst jk
  subst ijk
  dsimp only [correctedTensorAssociator]
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] using (rationalConstructibleScalar_coherence l E L i Y M j D hl).2.2 N k K

end

section
universe w₁ v₁ u₁
variable {I : Type w₁} [Preorder I] {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
private theorem uniqueStageSystem (S : StageSystem C) :
    ∃! R : StageSystem C,
      (∀ (i j : I) (h : i ≤ j), R.T h = S.T h) ∧
      (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), HEq (R.assoc h h') (S.assoc h h')) := by
  refine ⟨S, ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨T, a, c⟩ ⟨hT, ha⟩
  have ht : @T = @S.T := by
    funext i j h
    exact hT i j h
  cases ht
  have he : @a = @S.assoc := by
    funext i j k h h'
    exact eq_of_heq (ha i j k h h')
  cases he
  rfl
end

section
universe w₁ v₁ u₁
variable {I : Type w₁} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)
private theorem stageRepresentatives (A B : S.PairCategory) :
    (∀ f : A ⟶ B, ∃ n hA hB u, f = StageSystem.PairCategory.mkHom n hA hB u) ∧
    (∀ (L M : {n : I // A.stage ≤ n ∧ B.stage ≤ n})
      (f : (S.T L.property.1).obj A.obj ⟶ (S.T L.property.2).obj B.obj)
      (g : (S.T M.property.1).obj A.obj ⟶ (S.T M.property.2).obj B.obj),
      StageSystem.PairCategory.mkHom L.val L.property.1 L.property.2 f =
          StageSystem.PairCategory.mkHom M.val M.property.1 M.property.2 g ↔
        ∃ (N : {n : I // A.stage ≤ n ∧ B.stage ≤ n}) (hL : L ≤ N) (hM : M ≤ N),
          S.tr hL f = S.tr hM g) := by
  constructor
  · intro f
    induction f using StageSystem.PairCategory.hom_induction with
    | h L hA hB f => exact ⟨L, hA, hB, f, rfl⟩
  · intro L M f g
    constructor
    · intro e
      obtain ⟨N, hL, hM, he⟩ :=
        (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mp e
      exact ⟨⟨N, L.property.1.trans hL, L.property.2.trans hL⟩, hL, hM, he⟩
    · rintro ⟨N, hL, hM, he⟩
      exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mpr
        ⟨N.val, hL, hM, he⟩

end

section
variable {C D : Type*} [Category* C] [Category* D]
private theorem additive_transport (P P' : Preadditive C) (Q Q' : Preadditive D)
    (hP : P = P') (hQ : Q = Q') (F : C ⥤ D)
    (h : @Functor.Additive C D _ _ P' Q' F) :
    @Functor.Additive C D _ _ P Q F := by
  cases hP
  cases hQ
  exact h
end

section
variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
private theorem exact_of_eq (F G : C ⥤ D) (e : F = G) [c : G.CommShift ℤ]
    [G.IsTriangulated] :
    letI : F.CommShift ℤ := cast (congrArg (fun H : C ⥤ D ↦ H.CommShift ℤ) e.symm) c
    F.IsTriangulated := by
  subst G
  exact inferInstance

end

private theorem compShift_of_heq
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (hF : F = F') (hG : G = G') (hH : H = H')
    [cF : F'.CommShift ℤ] [cG : G'.CommShift ℤ] [cH : H'.CommShift ℤ]
    (a : F ⋙ G ≅ H) (a' : F' ⋙ G' ≅ H') (ha : HEq a a')
    [NatTrans.CommShift a'.hom ℤ] :
    letI : F.CommShift ℤ := cast (congrArg (fun f : C ⥤ D ↦ f.CommShift ℤ) hF.symm) cF
    letI : G.CommShift ℤ := cast (congrArg (fun f : D ⥤ E ↦ f.CommShift ℤ) hG.symm) cG
    letI : H.CommShift ℤ := cast (congrArg (fun f : C ⥤ E ↦ f.CommShift ℤ) hH.symm) cH
    NatTrans.CommShift a.hom ℤ := by
  subst F'
  subst G'
  subst H'
  cases eq_of_heq ha
  exact inferInstance

section
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (Y : AlgebraicGeometry.Scheme.{u})
private theorem correctedAssocShift (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M)
    (k : E →ₐ[Padic l] M) (h : j.comp i = k)
    (hc : NatTrans.CommShift (rationalConstructibleScalarComp l E L i Y M j D hl).hom ℤ) :
    NatTrans.CommShift ((rationalConstructibleScalarComp l E L i Y M j D hl ≪≫
      eqToIso (congrArg (rationalScalarExtension D l hl E Y M) h)).hom) ℤ := by
  subst k
  simpa only [eqToIso_refl, Iso.trans_refl] using hc
end

namespace AlgebraicallyClosedCoefficients

attribute [local irreducible] rationalTriangulationDatum rationalScalarExtension
  rationalConstructibleScalarComp rationalConstructibleScalarUnit
  Padic.finiteCoefficientBase Padic.finiteCoefficientCompositum

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- Finite coefficient fields in the fixed closure.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Index := Padic.FiniteCoefficientFields l Ω

/-- A finite-dimensional coefficient field has a model in every site universe.
The finite-basis coordinate equivalence constructs its Small proof without an axiom.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance coefficientSmall (E : Index l Ω) : Small.{u} E.val :=
  small_map (Module.finBasis (Padic l) E.val).equivFun.toEquiv

/-- The canonical size transport of a finite field to the scheme's universe.
Its algebra equivalence is Shrink.algEquiv; no coefficient closure/site size equality
is imposed. Source: blueprint order 1462
(blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Coefficient (E : Index l Ω) : Type u := Shrink.{u} E.val

/-- Finite dimensionality survives the canonical size transport.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance coefficientFinite (E : Index l Ω) :
    FiniteDimensional (Padic l) (Coefficient.{u} l Ω E) :=
  Module.Finite.equiv (Shrink.algEquiv (Padic l) E.val).symm.toLinearEquiv

/-- Inclusion transported through the actual algebra equivalences of the small models.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def coefficientInclusion (E L : Index l Ω) (h : E ≤ L) :
    Coefficient.{u} l Ω E →ₐ[Padic l] Coefficient.{u} l Ω L :=
  (Shrink.algEquiv (Padic l) L.val).symm.toAlgHom.comp
    ((IntermediateField.inclusion h).comp (Shrink.algEquiv (Padic l) E.val).toAlgHom)

set_option linter.unusedSectionVars false in
/-- The size transports preserve identity and composition of field inclusions.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: expand the conjugated inclusions. The inverse algebra equivalences cancel;
extensionality reduces both identities to identity/composition of subtype inclusions. -/
theorem coefficientInclusion_laws :
    (∀ E : Index l Ω, coefficientInclusion.{u} l Ω E E le_rfl =
      AlgHom.id (Padic l) (Coefficient.{u} l Ω E)) ∧
    (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
      (coefficientInclusion.{u} l Ω L M k).comp (coefficientInclusion.{u} l Ω E L h) =
        coefficientInclusion.{u} l Ω E M (h.trans k)) := by
  constructor
  · intro E
    ext x
    simp [coefficientInclusion]
  · intro E L M h k
    ext x
    simp [coefficientInclusion]

/-- The specified raw rational stage, using its equivalent small coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def Stage (E : Index l Ω) :=
  rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
@[instance_reducible]
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  ScalarLocalization.category _ _ _

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
@[instance_reducible]
noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage D l hl Ω Y E) :=
  ScalarLocalization.preadditive _ _ _

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageZero (E : Index l Ω) :
    HasZeroObject (Stage D l hl Ω Y E) :=
  rationalConstructibleZero D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
@[instance_reducible]
noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage D l hl Ω Y E) ℤ :=
  rationalConstructibleShift D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShiftAdditive (E : Index l Ω) (n : ℤ) :
    (shiftFunctor (Stage D l hl Ω Y E) n).Additive :=
  rationalConstructibleShiftAdditive D l hl (Coefficient.{u} l Ω E) Y n

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
@[instance_reducible]
noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage D l hl Ω Y E) :=
  rationalConstructiblePretriangulated D l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTriangulated (E : Index l Ω) :
    IsTriangulated (Stage D l hl Ω Y E) :=
  rationalConstructibleTriangulated D l hl (Coefficient.{u} l Ω E) Y

/-- The actual finite-field scalar transition, with both coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transition (E L : Index l Ω) (h : E ≤ L) :
    Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L :=
  rationalScalarExtension D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The supplied scalar transition structure on the named rational stages.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).CommShift ℤ :=
  rationalConstructibleScalarCommShift D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The supplied scalar transition structure on the named rational stages.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionExact (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).IsTriangulated :=
  rationalConstructibleScalar_exact D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The supplied scalar transition structure on the named rational stages.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionAdditive (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).Additive :=
  rationalConstructibleScalar_additive D l hl (Coefficient.{u} l Ω E) Y
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The canonical scalar associator, with its tensor-generator normalization.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def tensorAssociator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k) :=
  correctedTensorAssociator D l hl (Coefficient l Ω E) (Coefficient l Ω L)
    (Coefficient l Ω M) Y (coefficientInclusion l Ω E L h)
    (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
    ((coefficientInclusion_laws l Ω).2 E L M h k)

/-- The tensor formula uniquely determines the associator, including its inverse.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
theorem associator_specification (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    ∃! a : transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k),
      a = tensorAssociator D l hl Ω Y E L M h k := by
  exact ⟨tensorAssociator D l hl Ω Y E L M h k, rfl, fun a ha ↦ ha⟩

/-- The normalized tensor isomorphism, sealed by its exact equality specification.
This avoids unfolding completed sheaf scalar extension during stage coherence checks.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k) :=
  (associator_specification D l hl Ω Y E L M h k).exists.choose

/-- The sealed associator is exactly the original tensor formula.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
theorem associator_formula (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    associator D l hl Ω Y E L M h k = tensorAssociator D l hl Ω Y E L M h k :=
  (associator_specification D l hl Ω Y E L M h k).exists.choose_spec

/-- The normalized scalar unit, transported through the coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def unitor (E : Index l Ω) : transition D l hl Ω Y E E le_rfl ≅
    𝟭 (Stage D l hl Ω Y E) :=
  eqToIso (congrArg (rationalScalarExtension D l hl
    (Coefficient.{u} l Ω E) Y (Coefficient.{u} l Ω E))
    ((coefficientInclusion_laws l Ω).1 E)) ≪≫
    rationalConstructibleScalarUnit l (Coefficient.{u} l Ω E) Y D hl

/-- The coefficient fields form a directed order by the recorded compositum.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance indexDirected : IsDirectedOrder (Index l Ω) where
  directed E L := ⟨Padic.finiteCoefficientCompositum l Ω E L,
    (Padic.finiteCoefficientFields_properties l Ω).1 E L⟩

/-- The base coefficient field supplies a stage, including for the empty scheme.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance indexNonempty : Nonempty (Index l Ω) :=
  ⟨Padic.finiteCoefficientBase l Ω⟩

/-- The normalized tensor associators satisfy the stage-system cocycle.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: rationalConstructibleScalar_coherence proves the tensor pentagon. The small
coefficient inclusions compose by coefficientInclusion_laws. Substitution gives the
displayed cocycle, including repeated fields and identity inclusions. -/
theorem associator_cocycle (E L M N : Index l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) (K : Stage D l hl Ω Y E) :
    (transition D l hl Ω Y M N m).map ((associator D l hl Ω Y E L M h k).hom.app K) ≫
        (associator D l hl Ω Y E M N (h.trans k) m).hom.app K =
      (associator D l hl Ω Y L M N k m).hom.app
          ((transition D l hl Ω Y E L h).obj K) ≫
        (associator D l hl Ω Y E L N h (k.trans m)).hom.app K := by
  simp only [associator_formula]
  dsimp only [tensorAssociator, transition]
  exact pentagon D l hl (Coefficient l Ω E) (Coefficient l Ω L)
    (Coefficient l Ω M) (Coefficient l Ω N) Y
    (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
    (coefficientInclusion l Ω M N m) (coefficientInclusion l Ω E M (h.trans k))
    (coefficientInclusion l Ω L N (k.trans m))
    (coefficientInclusion l Ω E N ((h.trans k).trans m))
    ((coefficientInclusion_laws l Ω).2 E L M h k)
    ((coefficientInclusion_laws l Ω).2 L M N k m)
    ((coefficientInclusion_laws l Ω).2 E M N (h.trans k) m)
    ((coefficientInclusion_laws l Ω).2 E L N h (k.trans m)) K

/-- The tensor transitions and associators uniquely determine the stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take T to be transition and assoc to be associator; associator_cocycle is
precisely the required coherence equation. Conversely the displayed equalities fix
all data fields of StageSystem; the remaining cocycle proof is proof irrelevant. -/
theorem stageSystem_existsUnique :
    ∃! S : StageSystem (Stage D l hl Ω Y),
      (∀ (E L : Index l Ω) (h : E ≤ L), S.T h = transition D l hl Ω Y E L h) ∧
      (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
        HEq (S.assoc h k) (associator D l hl Ω Y E L M h k)) := by
  let S : StageSystem (Stage D l hl Ω Y) :=
    { T := fun {E L} ↦ transition D l hl Ω Y E L
      assoc := fun {E L M} ↦ associator D l hl Ω Y E L M
      cocycle := fun {E L M N} ↦ associator_cocycle D l hl Ω Y E L M N }
  exact uniqueStageSystem S

/-- The stage system with exactly the specified tensor functors and associators.
It is chosen only from a theorem determining all its data uniquely.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def stageSystem : StageSystem (Stage D l hl Ω Y) :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose

/-- The prescribed transition equality, before unfolding the concrete system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
theorem stageSystem_transition (E L : Index l Ω) (h : E ≤ L) :
    (stageSystem D l hl Ω Y).T h = transition D l hl Ω Y E L h :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h

/-- The prescribed associator equality, before unfolding the concrete system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
theorem stageSystem_associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    HEq ((stageSystem D l hl Ω Y).assoc h k) (associator D l hl Ω Y E L M h k) :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.2 E L M h k

attribute [local irreducible] stageSystem

/-- The existing tensor functor as a transition of the uniquely fixed stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageTransition (E L : Index l Ω) (h : E ≤ L) :=
  (stageSystem D l hl Ω Y).T h

/-- The specified shift comparison transported by equality of the transition functors.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L ↦ F.CommShift ℤ)
    (stageSystem_transition D l hl Ω Y E L h).symm)
    (transitionCommShift D l hl Ω Y E L h)

/-- Exactness of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: stageSystem_existsUnique identifies this functor and its shift comparison
with the specified tensor extension. Apply rationalConstructibleScalar_exact. -/
@[instance]
theorem stageTransition_exact (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).IsTriangulated := by
  exact exact_of_eq _ _
    (stageSystem_transition D l hl Ω Y E L h)

/-- Additivity of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: equality of functors with transition reduces the claim to transitionAdditive. -/
@[instance]
theorem stageTransition_additive (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).Additive := by
  unfold stageTransition
  rw [stageSystem_transition D l hl Ω Y E L h]
  exact transitionAdditive D l hl Ω Y E L h

private theorem associator_commShift (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    NatTrans.CommShift (associator D l hl Ω Y E L M h k).hom ℤ := by
  rw [associator_formula]
  unfold tensorAssociator
  rw [correctedTensorAssociator_formula]
  exact correctedAssocShift D l hl (Coefficient l Ω E) (Coefficient l Ω L)
    (Coefficient l Ω M) Y _ _ _ ((coefficientInclusion_laws l Ω).2 E L M h k)
    (rationalConstructibleScalarComp_commShift D l hl (Coefficient l Ω E) Y
      (Coefficient l Ω L) (coefficientInclusion l Ω E L h)
      (Coefficient l Ω M) (coefficientInclusion l Ω L M k))

/-- The prescribed stage associators commute with shifts.
Source: scalar extension tensor coherence
(blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageAssociatorCommShift
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    NatTrans.CommShift ((stageSystem D l hl Ω Y).assoc h k).hom ℤ := by
  have : NatTrans.CommShift (associator D l hl Ω Y E L M h k).hom ℤ :=
    associator_commShift D l hl Ω Y E L M h k
  exact compShift_of_heq _ _ _ _ _ _
    (stageSystem_transition D l hl Ω Y E L h)
    (stageSystem_transition D l hl Ω Y L M k)
    (stageSystem_transition D l hl Ω Y E M (h.trans k)) _ _
    (stageSystem_associator D l hl Ω Y E L M h k)

attribute [local irreducible] stageCategory stagePreadditive stageShift stagePretriangulated

/-- The upstream common-stage pair category, specialized to the specified rational stages.
Its objects are literal pairs, and no idempotents are adjoined.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Pair := (stageSystem D l hl Ω Y).PairCategory

/-- Cache the existing upstream category on the named concrete pair type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
@[instance_reducible]
noncomputable instance pairCategory : Category (Pair D l hl Ω Y) :=
  StageSystem.instCategoryPairCategory (stageSystem D l hl Ω Y)

variable {D l hl Ω Y}

/-- The directed index of common finite coefficient overfields of two pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Common (A B : Pair D l hl Ω Y) :=
  {L : Index l Ω // A.stage ≤ L ∧ B.stage ≤ L}

/-- Hom at one common coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def StageHom (A B : Pair D l hl Ω Y) (L : Common A B) :=
  ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj)

/-- Cache the abelian group of a stage Hom before forming the dependent colimit family.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
@[instance_reducible]
noncomputable instance stageHomAddCommGroup (A B : Pair D l hl Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  (stagePreadditive D l hl Ω Y L.val).homGroup _ _

/-- Extend the representative and conjugate by the specified associators.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transport (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  (stageSystem D l hl Ω Y).tr h f

/-- Transport is additive and preserves zero.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: scalar extension is additive. Left and right composition by each fixed
associator component are additive by preadditivity of the rational target stage. -/
theorem transport_additive (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    transport A B L M h 0 = 0 ∧
      ∀ f g, transport A B L M h (f + g) =
        transport A B L M h f + transport A B L M h g := by
  exact ⟨StageSystem.tr_zero (S := stageSystem D l hl Ω Y) (hi := L.property.1)
      (hj := L.property.2) (x := A.obj) (y := B.obj) h,
    fun f g ↦ StageSystem.tr_add (S := stageSystem D l hl Ω Y) h f g⟩

/-- The transition homomorphism of the directed Hom system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transportHom (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

/-- Decidable equality is used only to realize Mathlib's algebraic direct limit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDecidableEq (A B : Pair D l hl Ω Y) :
    DecidableEq (Common A B) := Classical.decEq _

/-- The actual abelian-group colimit, with no completion of its objects.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def ColimitHom (A B : Pair D l hl Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

/-- The direct limit's abelian group structure, on the fixed Hom type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance colimitHomGroup (A B : Pair D l hl Ω Y) :
    AddCommGroup (ColimitHom A B) :=
  AddCommGroup.DirectLimit.addCommGroup (StageHom A B) (transportHom A B)

/-- The class of a map over a common finite coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def colimitOf (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : ColimitHom A B :=
  AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B) ⟨L, hA, hB⟩ f

/-- The upstream quotient Hom has exactly the stated abelian-colimit coordinates.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: send each common-stage representative to its direct-limit class. The tensor
cocycle and unit law make transport a directed system; the quotient relation is exactly
equality after extension. The direct-limit representative criterion therefore makes
this map well-defined and bijective. Every Hom is represented, proving uniqueness. -/
theorem homCoordinates_existsUnique (A B : Pair D l hl Ω Y) :
    ∃! e : (A ⟶ B) ≃ ColimitHom A B,
      ∀ (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f : StageHom A B ⟨L, hA, hB⟩),
        e (StageSystem.PairCategory.mkHom L hA hB f) = colimitOf A B L hA hB f := by
  let J := Common A B
  let G := StageHom A B
  let t := transportHom A B
  let : DecidableEq J := Classical.decEq _
  let : Nonempty J := by
    obtain ⟨n, hA, hB⟩ := exists_ge_ge A.stage B.stage
    exact ⟨⟨n, hA, hB⟩⟩
  let : IsDirectedOrder J := ⟨fun n m ↦ by
    obtain ⟨p, hn, hm⟩ := exists_ge_ge n.val m.val
    exact ⟨⟨p, n.property.1.trans hn, n.property.2.trans hn⟩, hn, hm⟩⟩
  let q (n : J) : G n →+ (A ⟶ B) :=
    { toFun := StageSystem.PairCategory.mkHom n.val n.property.1 n.property.2
      map_zero' := StageSystem.PairCategory.mkHom_zero _ _
      map_add' := fun _ _ ↦ (StageSystem.PairCategory.mkHom_add _ _).symm }
  let back : AddCommGroup.DirectLimit G t →+ (A ⟶ B) :=
    AddCommGroup.DirectLimit.lift G t _ q (fun n m h f ↦ by
      exact StageSystem.PairCategory.mkHom_tr (X := A) (Y := B) h f)
  let forward : (A ⟶ B) → AddCommGroup.DirectLimit G t :=
    Quotient.lift
      (fun r : StageSystem.PairCategory.Rep A B ↦
        AddCommGroup.DirectLimit.of G t ⟨r.k, r.hX, r.hY⟩ r.u)
      (by
        intro r s h
        obtain ⟨p, hr, hs, he⟩ := h
        let n : J := ⟨p, r.hX.trans hr, r.hY.trans hr⟩
        have he' : t ⟨r.k, r.hX, r.hY⟩ n hr r.u =
            t ⟨s.k, s.hX, s.hY⟩ n hs s.u := by
          exact he
        exact (AddCommGroup.DirectLimit.of_f (G := G) (f := t) (i := ⟨r.k, r.hX, r.hY⟩)
          (j := n) hr r.u).symm.trans
            ((congrArg (AddCommGroup.DirectLimit.of G t n) he').trans
              (AddCommGroup.DirectLimit.of_f (G := G) (f := t)
                (i := ⟨s.k, s.hX, s.hY⟩) (j := n) hs s.u)))
  let e : (A ⟶ B) ≃ AddCommGroup.DirectLimit G t :=
    { toFun := forward
      invFun := back
      left_inv := by
        intro f
        induction f using StageSystem.PairCategory.hom_induction with
        | h n hA hB f => exact AddCommGroup.DirectLimit.lift_of _ _ _ _ _
      right_inv := by
        intro f
        induction f using AddCommGroup.DirectLimit.induction_on with
        | ih n f =>
          change forward (back (AddCommGroup.DirectLimit.of G t n f)) = _
          rw [AddCommGroup.DirectLimit.lift_of]
          rfl }
  refine ⟨e, fun _ _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Equiv.ext
  intro f
  induction f using StageSystem.PairCategory.hom_induction with
  | h n hA hB f => exact he' n hA hB f

/-- The canonical Hom coordinates, fixed on every common-stage representative.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def homCoordinates (A B : Pair D l hl Ω Y) :=
  (homCoordinates_existsUnique A B).exists.choose

/-- The map represented at L, using the existing upstream quotient constructor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev ofHom (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : A ⟶ B :=
  StageSystem.PairCategory.mkHom L hA hB f

private lemma coordinates_ofHom (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : StageHom A B ⟨L, hA, hB⟩) :
    homCoordinates A B (ofHom A B L hA hB f) = colimitOf A B L hA hB f :=
  (homCoordinates_existsUnique A B).exists.choose_spec L hA hB f

/-- Colimit coordinates preserve the native quotient addition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
private theorem nativeCoordinates_add {A B : Pair D l hl Ω Y} (f g : A ⟶ B) :
    homCoordinates A B (f + g) = homCoordinates A B f + homCoordinates A B g := by
  obtain ⟨L, -, hA, hB, -, -, u, w, rfl, rfl⟩ :=
    StageSystem.PairCategory.exists_common_stage f g A.stage
  rw [StageSystem.PairCategory.mkHom_add, coordinates_ofHom,
    coordinates_ofHom, coordinates_ofHom]
  exact map_add (AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B)
    ⟨L, hA, hB⟩) u w

/-- The abelian group transported from the specified directed colimit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance homAddCommGroup (A B : Pair D l hl Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

private theorem homGroup_eq_native (A B : Pair D l hl Ω Y) :
    homAddCommGroup A B = StageSystem.PairCategory.instAddCommGroupHom A B := by
  apply AddCommGroup.ext
  funext f g
  change (homCoordinates A B).symm
    (homCoordinates A B f + homCoordinates A B g) = f + g
  apply (homCoordinates A B).injective
  exact ((homCoordinates A B).apply_symm_apply _).trans (nativeCoordinates_add f g).symm

attribute [-instance] StageSystem.PairCategory.instAddHom
  StageSystem.PairCategory.instAddCommGroupHom StageSystem.PairCategory.preadditive in
/-- The fixed composition is additive in each variable.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: represent the three maps at a common compositum. Colimit structure maps are
additive and stage composition is bilinear, giving both asserted equations. -/
theorem composition_bilinear :
    (∀ (A B C : Pair D l hl Ω Y) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : Pair D l hl Ω Y) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  have hadd {A B : Pair D l hl Ω Y} (f g : A ⟶ B) :
      (homCoordinates A B).symm (homCoordinates A B f + homCoordinates A B g) =
        @Add.add (A ⟶ B) (StageSystem.PairCategory.instAddHom A B) f g := by
    apply (homCoordinates A B).injective
    exact ((homCoordinates A B).apply_symm_apply _).trans (nativeCoordinates_add f g).symm
  let : Preadditive (Pair D l hl Ω Y) :=
    StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y)
  constructor
  · intro A B C f f' g
    change (homCoordinates A B).symm (homCoordinates A B f + homCoordinates A B f') ≫ g =
      (homCoordinates A C).symm
        (homCoordinates A C (f ≫ g) + homCoordinates A C (f' ≫ g))
    rw [hadd, hadd]
    exact Preadditive.add_comp A B C f f' g
  · intro A B C f g g'
    change f ≫ (homCoordinates B C).symm (homCoordinates B C g + homCoordinates B C g') =
      (homCoordinates A C).symm
        (homCoordinates A C (f ≫ g) + homCoordinates A C (f ≫ g'))
    rw [hadd, hadd]
    exact Preadditive.comp_add A B C f g g'

/-- Preadditivity uses the actual colimit abelian groups.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance preadditive : Preadditive (Pair D l hl Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

private theorem preadditive_eq_native :
    preadditive (D := D) (l := l) (hl := hl) (Ω := Ω) (Y := Y) =
      StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y) := by
  apply Preadditive.ext
  funext A B
  exact homGroup_eq_native A B

/-- The existing upstream inclusion of the actual rational finite stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev inclusion (E : Index l Ω) : Stage D l hl Ω Y E ⥤ Pair D l hl Ω Y :=
  (stageSystem D l hl Ω Y).ι E

/-- The inclusion preserves the abelian-colimit addition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: inclusion sends f to its normalized representative, and homCoordinates sends
that representative to its direct-limit class. Both normalization by fixed unit
components and the direct-limit structure maps are additive. -/
@[instance]
theorem inclusion_additive (E : Index l Ω) : (inclusion E : Stage D l hl Ω Y E ⥤ _).Additive := by
  have h : @Functor.Additive _ _ _ _ (stagePreadditive D l hl Ω Y E)
      (StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y)) (inclusion E) :=
    inferInstance
  exact additive_transport _ _ _ _ rfl preadditive_eq_native _ h

/-- Every class has a finite representative, and equality is equality at a later stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: composita make each common-overfield index nonempty and directed. The normalized
tensor unit and associator pentagon make transport an actual directed system. Apply
Mathlib's directed-colimit representation and zero-exactness criteria to the difference
of two representatives. This gives precisely equality after one further extension. -/
theorem representatives (A B : Pair D l hl Ω Y) :
    (∀ f : A ⟶ B, ∃ (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (u : StageHom A B ⟨L, hA, hB⟩), f = ofHom A B L hA hB u) ∧
    (∀ (L M : Common A B) (f : StageHom A B L) (g : StageHom A B M),
      ofHom A B L.val L.property.1 L.property.2 f =
          ofHom A B M.val M.property.1 M.property.2 g ↔
        ∃ (N : Common A B) (hL : L ≤ N) (hM : M ≤ N),
          transport A B L N hL f = transport A B M N hM g) := by
  exact stageRepresentatives (stageSystem D l hl Ω Y) A B

/-- Stagewise object shift, with the coefficient field unchanged.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftPair (n : ℤ) (A : Pair D l hl Ω Y) : Pair D l hl Ω Y :=
  ⟨A.stage, (shiftFunctor (Stage D l hl Ω Y A.stage) n).obj A.obj⟩

/-- The shifted representative uses the prescribed scalar-extension shift comparison.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftRepresentative (n : ℤ) (A B : Pair D l hl Ω Y)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) :
    StageHom (shiftPair n A) (shiftPair n B) ⟨L, hA, hB⟩ :=
  ((stageTransition D l hl Ω Y A.stage L hA).commShiftIso n).hom.app A.obj ≫
    (shiftFunctor (Stage D l hl Ω Y L) n).map f ≫
    ((stageTransition D l hl Ω Y B.stage L hB).commShiftIso n).inv.app B.obj

/-- The stagewise shift with the representative formula of shift_exists.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance hasShift : HasShift (Pair D l hl Ω Y) ℤ :=
  StageSystem.PairCategory.hasShift (stageSystem D l hl Ω Y) ℤ

/-- Each induced integer shift is additive.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair D l hl Ω Y) n).Additive := by
  have h : @Functor.Additive _ _ _ _
      (StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y))
      (StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y))
      (shiftFunctor (Pair D l hl Ω Y) n) := by
    let : Preadditive (Pair D l hl Ω Y) :=
      StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y)
    change ((stageSystem D l hl Ω Y).shiftMorphism ℤ n).functor.Additive
    infer_instance
  exact additive_transport _ _ _ _ preadditive_eq_native preadditive_eq_native _ h

/-- The normalized exact-stage shift comparison, fixed to identity on shifted pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ :=
  StageSystem.ι_commShift E

attribute [-instance] StageSystem.PairCategory.instZeroHom in
/-- A stage zero object remains zero after forming directed Hom colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take the zero object at the bottom coefficient field. Every transition is exact
and therefore preserves zero. At every common field its Hom groups to and from any
object vanish. Their directed colimits vanish, giving the zero-object universal property. -/
theorem zero_exists : HasZeroObject (Pair D l hl Ω Y) := by
  let E : Index l Ω := Padic.finiteCoefficientBase l Ω
  refine ⟨⟨(inclusion E).obj 0, ?_⟩⟩
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 _ = (inclusion E).map (𝟙 (0 : Stage D l hl Ω Y E)) :=
      ((inclusion E).map_id _).symm
    _ = (inclusion E).map 0 := congrArg (inclusion E).map ((isZero_zero _).eq_of_src _ _)
    _ = 0 := (inclusion E).map_zero _ _

attribute [instance] zero_exists

/-- The canonical coefficient-stage identifications commute with shifts.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: on finite representatives this is scalar-extension shift compatibility and
rationalConstructibleScalar_coherence. The normalized inclusion comparisons are
identities on shifted pairs. The cocycle equation identifies both composites. -/
@[instance]
theorem transitionIso_commShift (E L : Index l Ω) (h : E ≤ L) :
    NatTrans.CommShift ((stageSystem D l hl Ω Y).transIso h).hom ℤ := by
  exact StageSystem.transIso_commShift (S := stageSystem D l hl Ω Y) (A := ℤ) h

/-- The recorded common-stage distinguished-triangle criterion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Distinguished (T : Triangle (Pair D l hl Ω Y)) : Prop :=
  (stageSystem D l hl Ω Y).CommonStageDistinguished T

/-- The unique pretriangulation supplied by the common-stage Verdier theorem.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pretriangulated : Pretriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose

/-- The Verdier axiom for the specified common-stage triangles.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance isTriangulated : IsTriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.1

/-- Each actual rational finite-stage inclusion is exact.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusion_exact (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).IsTriangulated :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.2 E

/-- The triangle criterion, exposing the finite-field-of-definition clause.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: this is the distinguished-set clause of commonStage_verdier_existsUnique
for the actual scalar-extension stage system. -/
theorem distinguished_iff (T : Triangle (Pair D l hl Ω Y)) :
    T ∈ distTriang (Pair D l hl Ω Y) ↔ Distinguished T := by
  exact (StageSystem.commonStage_verdier_existsUnique
    (stageSystem D l hl Ω Y)).exists.choose_spec.1 T

end AlgebraicallyClosedCoefficients

end WeilConjectures
