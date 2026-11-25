/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AffineSpaceRationalLine
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AffineSpaceRationalGeometry
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalAffineTensorCalculus
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalAffineAdjunctionCalculus

/-!
# Rational purity for relative affine space in every dimension

Source: blueprint main-20261015, chap-Construction-of-f,
`sk-cor-affine-space-rational/sk-cor-affine-space-rational-induction.md` and its proof
(blueprint: theorem-f-shriek-ell-adic-coefficients).

The functors act on the literal localizing closures of the bounded constructible
module-object categories. Their comparisons with the ambient functors specify both
objects and maps. The Tate line is the existing signed power, transported back through
the existing equivalence with sectionwise modules before applying derived tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Derived tensor with the degree-d Tate line, in the internal-module encoding.
The signed line is the recorded tensor power; the existing sectionwise/internal module
equivalence changes only its presentation, not its coefficient ring or underlying sheaf.
Source: blueprint definition-tate-twists, positive powers and derived twist formula
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
def rationalDegreeTwistFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (d : ℕ) :=
  rationalTwistFunctor Λ X
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).inverse.obj
        (spSignedTwist X (condensedRingObj Λ X) L (d : ℤ)))

/-- The Nagata compactification chosen in the chapter setting, for the projection
of relative affine d-space. The displayed over-objects and their instances are the
same canonical structure morphisms as those of the affine projection.
Source: blueprint sk-def-sfb-dc-setting, chosen compactification convention
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
def affineSpaceChosenCompactification
    (k : Type u) [Field k] (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))] (d : ℕ) :
    Compactification (𝔸(ULift.{u} (Fin d); V) ↘ V) :=
  @compactificationOverField k _
    (Over.mk ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k))))
    (Over.mk (V ↘ Spec (.of k)))
    (inferInstanceAs (LocallyOfFiniteType
      ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact
      ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (IsSeparated
      ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k)))))
    (inferInstanceAs (QuasiCompact (V ↘ Spec (.of k))))
    (inferInstanceAs (IsSeparated (V ↘ Spec (.of k))))
    (Over.homMk (𝔸(ULift.{u} (Fin d); V) ↘ V) rfl)

/-- The ambient functor p_d^*(d)[2d], with the specified degree-d Tate tensor functor.
Source: blueprint sk-cor-affine-space-rational-induction, both conclusions
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
def affineSpaceRationalPullTwistShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (V : Scheme.{u}) (d : ℕ)
    (twist : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V)))) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V))))) :=
  (CondensedRing.upperStar Λ (𝔸(ULift.{u} (Fin d); V) ↘ V)).leftDerivedFunctor ⋙
    twist ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- The two assertions for one rational coefficient convention. The functors F and P
are restrictions of the specified compactification lower shriek and twisted shifted
pullback, as witnessed by natural isomorphisms after the full inclusions. The adjunction
ensures existence of the exceptional right adjoint; every such adjoint G is isomorphic to P.
The final conjunct is preservation of Dbc by the ambient twisted shifted pullback itself.
Source: blueprint sk-cor-affine-space-rational-induction, entire statement
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
def affineSpaceRationalAssertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (V : Scheme.{u}) (d : ℕ)
    (c : Compactification (𝔸(ULift.{u} (Fin d); V) ↘ V))
    (twist : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V)))) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin d); V))) Ab.{u + 1})
          (condensedRingObj Λ (𝔸(ULift.{u} (Fin d); V))))) : Prop :=
  (∃ (F : rationalLocalizingCategory Λ (𝔸(ULift.{u} (Fin d); V)) ⥤
        rationalLocalizingCategory Λ V)
      (P : rationalLocalizingCategory Λ V ⥤
        rationalLocalizingCategory Λ (𝔸(ULift.{u} (Fin d); V)))
      (_hF : F ⋙ rationalLocalizingInclusion Λ V ≅
        rationalLocalizingInclusion Λ (𝔸(ULift.{u} (Fin d); V)) ⋙
          rightDerivedLowerShriekOfCompactification Λ c)
      (_hP : P ⋙ rationalLocalizingInclusion Λ (𝔸(ULift.{u} (Fin d); V)) ≅
        rationalLocalizingInclusion Λ V ⋙ affineSpaceRationalPullTwistShift Λ V d twist)
      (_adjP : F ⊣ P),
      ∀ (G : rationalLocalizingCategory Λ V ⥤
          rationalLocalizingCategory Λ (𝔸(ULift.{u} (Fin d); V))),
        Nonempty (F ⊣ G) → Nonempty (G ≅ P)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)),
      constantModelBoundedConstructible Λ V K →
        constantModelBoundedConstructible Λ (𝔸(ULift.{u} (Fin d); V))
          ((affineSpaceRationalPullTwistShift Λ V d twist).obj K))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalCompactSupportAdjunction_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (b : Compactification g)
    (H : (X ⟶ Y) → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    RationalCompactSupportAdjunction Λ (h.symm ▸ b) (H f) →
      RationalCompactSupportAdjunction Λ b (H g) := by
  cases h
  exact id

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalAffineInductionAux
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (d : ℕ) :
    ∀ (V : Scheme.{u}) [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
      [IsSeparated (V ↘ Spec (.of k))]
      (b : Compactification (𝔸(ULift.{u} (Fin d); V) ↘ V)),
      RationalCompactSupportAdjunction (RationalP1.coefficient ℓ c).X b
        (rationalTatePull ℓ c (𝔸(ULift.{u} (Fin d); V) ↘ V) d) := by
  obtain ⟨_, hcomp⟩ := rationalAffineTensorCalculus ℓ c k
  have hzero (X : Scheme.{u}) := rationalTatePowerZeroIso
    (RationalP1.coefficient ℓ c).X X (RationalP1.line ℓ c X)
  have hone (X : Scheme.{u}) := rationalTatePowerOneIso
    (RationalP1.coefficient ℓ c).X X (RationalP1.line ℓ c X)
  have hzeroPull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      Nonempty (rationalTatePull ℓ c f 0 ≅
        (upperStar (RationalP1.coefficient ℓ c).X f).leftDerivedFunctor) := by
    intro X Y f
    obtain ⟨e⟩ := hzero X
    exact ⟨Functor.isoWhiskerLeft _ e ≪≫ Functor.rightUnitor _⟩
  induction d with
  | zero =>
    intro V _ _ _ _ b
    have := rationalAffineZero_isIso V
    exact (rationalOpenCompactSupportAdjunction ℓ c k _ b).ofIso _
      (Classical.choice (hzeroPull _)).symm
  | succ d ih =>
    intro V _ _ _ _ b
    let W := 𝔸(ULift.{u} (Fin d); V)
    let T := 𝔸(PUnit.{u + 1}; W)
    let X := 𝔸(ULift.{u} (Fin (d + 1)); V)
    let p : W ⟶ V := W ↘ V
    let q : T ⟶ W := T ↘ W
    have : LocallyOfFiniteType (W ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (p ≫ (V ↘ Spec (.of k))))
    have : QuasiCompact (W ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (p ≫ (V ↘ Spec (.of k))))
    have : IsSeparated (W ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated (p ≫ (V ↘ Spec (.of k))))
    have : LocallyOfFiniteType (T ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (q ≫ (W ↘ Spec (.of k))))
    have : QuasiCompact (T ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (q ≫ (W ↘ Spec (.of k))))
    have : IsSeparated (T ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated (q ≫ (W ↘ Spec (.of k))))
    have : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType ((X ↘ V) ≫ (V ↘ Spec (.of k))))
    have : QuasiCompact (X ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact ((X ↘ V) ≫ (V ↘ Spec (.of k))))
    have : IsSeparated (X ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated ((X ↘ V) ≫ (V ↘ Spec (.of k))))
    let e : X ≅ T := rationalAffineSuccIso V d
    have hproj : (e.hom ≫ q) ≫ p = X ↘ V := by
      simpa only [Category.assoc] using rationalAffineSuccIso_over V d
    have heV : e.hom ≫ (T ↘ Spec (.of k)) = X ↘ Spec (.of k) := by
      change e.hom ≫ (q ≫ p ≫ (V ↘ Spec (.of k))) = _
      rw [← Category.assoc, ← Category.assoc, hproj]
      rfl
    have : e.hom.IsOver (Spec (.of k)) := ⟨heV⟩
    let bp := affineSpaceChosenCompactification k V d
    let bq := affineLineChosenCompactification k W
    let be := Compactification.ofIsOpenImmersion e.hom
    let beq := bq.precomp e.hom
    let ball : Compactification ((e.hom ≫ q) ≫ p) := hproj.symm ▸ b
    have hp := ih V bp
    have hl : affineLineRationalAssertion (RationalP1.coefficient ℓ c).X W bq
        (fun Y ↦ rationalTwistFunctor (RationalP1.coefficient ℓ c).X Y
          (RationalP1.line ℓ c Y)) := by
      cases c with
      | none => exact (det_cor_affine_space_rational_line ℓ k W).2
      | some E => exact (det_cor_affine_space_rational_line ℓ k W).1 E
    obtain ⟨J, R, hJ, hR, adjJ, F, Q, hF, hQ, hFQ, P, hP, adjP, _⟩ := hl
    have hq : RationalCompactSupportAdjunction (RationalP1.coefficient ℓ c).X bq
        (rationalTatePull ℓ c q 1) := by
      refine ⟨F, P, ⟨hF⟩, ⟨?_⟩, ⟨adjP⟩⟩
      let eone := Classical.choice (hone T)
      exact hP ≪≫ Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft _ eone.symm) (shiftFunctor _ (2 : ℤ)))
    have he : RationalCompactSupportAdjunction (RationalP1.coefficient ℓ c).X be
        (rationalTatePull ℓ c e.hom 0) :=
      (rationalOpenCompactSupportAdjunction ℓ c k e.hom be).ofIso _
        (Classical.choice (hzeroPull e.hom)).symm
    have heq := rationalCompactSupportAdjunction_comp ℓ c k e.hom q be bq beq _ _ he hq
    obtain ⟨ceq⟩ := hcomp X T W e.hom q 1 0
    have heq' := heq.ofIso _ ceq
    have hall := rationalCompactSupportAdjunction_comp ℓ c k (e.hom ≫ q) p
      beq bp ball _ _ heq' hp
    obtain ⟨call⟩ := hcomp X W V (e.hom ≫ q) p d 1
    have hall' := hall.ofIso _ call
    exact rationalCompactSupportAdjunction_transport _ hproj b
      (fun f ↦ rationalTatePull ℓ c f (d + 1)) hall'

/-- Rational affine-space exceptional purity in every natural dimension, together
with preservation of bounded constructibility by p_d^*(d)[2d]. This includes d = 0,
all finite coefficient subextensions, and the finite-subextension-valued algebraic closure.
Source: blueprint sk-cor-affine-space-rational-induction, statement and proof
(blueprint: theorem-f-shriek-ell-adic-coefficients).

Proof, following the seven DAG steps:
1. Put T_X = Loc(Dbc(X)). By det-def-localizing-closure-ctf-equals-bc the rational
   finite-Tor and bounded-constructible categories agree, as do their closures.
   proposition-proper-base-change-localizing-categories--1 makes every inverse image exact,
   coproduct-preserving, and preserving Dbc and these precise closures.
2. The degree-one Tate line of definition-tate-twists is locally free of rank one.
   Tensor with its dual is inverse to tensor with it. Thus its powers give exact
   coproduct-preserving tensor equivalences. On a common pro-etale trivializing
   cover they preserve finite constant scalar models and all vanishing degrees.
   They preserve Dbc, hence its localizing closure by the defining minimality of
   definition-localizing-subcategory. Shifts reindex cohomology and preserve both categories.
3. lemma-inverse-image-coefficient-sheaves identifies the pulled-back Tate lines.
   The strong monoidal inverse image and scalar comparison of prose-03-02
   give the tensor comparison, invertible locally where the line is trivial.
   Apply termwise to obtain pullback/twist/shift compatibility. Use the mate
   def-sfb-module-upper-star-comp for pullback composition. Reassociate the recorded
   tensor powers and add shifts to identify successive twists and shifts.
4. Induct on d uniformly over every base V in the setting. For d = 0 the affine
   projection is canonically the identity. Compare its chosen compactification with
   the identity by proposition-construction-independence-rf-shriek. Its lower shriek is therefore
   the identity; theorem-existence-exceptional-inverse-image and adjoint uniqueness identify its
   exceptional inverse image with the identity. The zero Tate power and shift give that functor.
5. lem-sfb-localizing-lower-shriek-composition and the adjunctions of
   theorem-existence-exceptional-inverse-image give Hom(Rb_! Ra_! M,N) = Hom(M,a^! b^! N),
   naturally. Uniqueness of the right adjoint gives (ba)^! isomorphic to a^! b^! on T.
6. For the step r to r+1 set W = A^r_V and let pi : A^1_W -> W be the projection.
   The polynomial-coordinate isomorphism phi : A^(r+1)_V -> A^1_W gives
   p_(r+1) = p_r pi phi. Finite polynomial generators and the closed diagonal show
   W is again separated finite type over k. For phi, compare with its proper
   compactification by proposition-construction-independence-rf-shriek; uniqueness gives phi^! =
   phi^*. Apply theorem-f-shriek-ell-adic-coefficients over W, the inductive hypothesis,
   and Step 5 twice. Move the twists and shifts through the pullbacks by Step 3,
   compose the pullbacks, then add the exponents and shifts to obtain (r+1)[2r+2].
7. For K in Dbc(V), Step 1 puts p_d^*K in Dbc and Step 2 preserves it under the
   degree-d twist and [2d]. A cohomological interval [a,b] becomes [a-2d,b-2d].
   This also handles the empty base and the zero complex. The natural isomorphism
   in Step 6 holds on the full localizing categories, including unbounded objects.
-/
theorem affineSpace_rational_induction
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (V : Scheme.{u}) [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))]
    [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (d : ℕ) :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      affineSpaceRationalAssertion (Profinite.continuousMapRingObj E.1) V d
        (affineSpaceChosenCompactification k V d)
        (rationalDegreeTwistFunctor (Profinite.continuousMapRingObj E.1)
          (𝔸(ULift.{u} (Fin d); V)) (spRationalTwist (𝔸(ULift.{u} (Fin d); V)) ℓ E) d)) ∧
    affineSpaceRationalAssertion (Profinite.padicAlgClRingObj ℓ) V d
      (affineSpaceChosenCompactification k V d)
      (rationalDegreeTwistFunctor (Profinite.padicAlgClRingObj ℓ)
        (𝔸(ULift.{u} (Fin d); V)) (spQbarTwist (𝔸(ULift.{u} (Fin d); V)) ℓ) d) := by
  have h : ∀ c : Option (PadicAlgCl.FiniteIntermediateField ℓ),
      affineSpaceRationalAssertion (RationalP1.coefficient ℓ c).X V d
        (affineSpaceChosenCompactification k V d)
        (rationalDegreeTwistFunctor (RationalP1.coefficient ℓ c).X
          (𝔸(ULift.{u} (Fin d); V)) (RationalP1.line ℓ c _) d) := by
    intro c
    obtain ⟨F, P, ⟨hF⟩, ⟨hP⟩, ⟨adj⟩⟩ :=
      rationalAffineInductionAux ℓ c k d V (affineSpaceChosenCompactification k V d)
    refine ⟨⟨F, P, hF, hP, adj, ?_⟩, ?_⟩
    · intro G ⟨adjG⟩
      exact ⟨adjG.rightAdjointUniq adj⟩
    · have : LocallyOfFiniteType (𝔸(ULift.{u} (Fin d); V) ↘ Spec (.of k)) :=
        inferInstanceAs (LocallyOfFiniteType
          ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k))))
      have : QuasiCompact (𝔸(ULift.{u} (Fin d); V) ↘ Spec (.of k)) :=
        inferInstanceAs (QuasiCompact
          ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k))))
      have : IsSeparated (𝔸(ULift.{u} (Fin d); V) ↘ Spec (.of k)) :=
        inferInstanceAs (IsSeparated
          ((𝔸(ULift.{u} (Fin d); V) ↘ V) ≫ (V ↘ Spec (.of k))))
      exact (rationalAffineTensorCalculus ℓ c k).1 _ _ _ d
  exact ⟨fun E ↦ h (some E), h none⟩

end AlgebraicGeometry.ProEtale.CondensedRing
