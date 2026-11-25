/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory

/-! # Scalar action on the intrinsic finite-stage pair category

Source: blueprint def-weil-pbc-qbar-category, scalar-action and pair-category paragraphs
(blueprint: def-weil-pbc-qbar-category).

Retain the published legacy interface. On the current intrinsic rational stages, use
exactly the same finite-compositum scalar construction. Objects, Hom classes, shifts and
common-stage cone triangles are the already recorded intrinsic ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The coefficient identification is normalized on integral fractions, followed
by the fixed small-model equivalence. Source: blueprint scalar-action paragraph
(blueprint: def-weil-pbc-qbar-category). -/
def intrinsicQbarStageFieldEquiv (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    Localization.Away (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)) ≃+* E.val :=
  (sfRationalCoefficientEquiv l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).toRingEquiv.trans
    (Shrink.algEquiv ℚ_[l] E.val).toRingEquiv

/-- Cache the existing localized-ring linear structure on the named rational stage.
Source: blueprint finite-stage scalar convention
(blueprint: def-weil-pbc-qbar-category). -/
instance intrinsicQbarStageLocalizedLinear (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    Linear (Localization.Away (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)))
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :=
  inferInstanceAs (Linear (Localization.Away (Padic.coefficientExtensionUniformizer l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)))
    (sfRationalConstructibleCategory l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y))

/-- Transport finite-field scalar action through the normalized coefficient equivalence.
Source: blueprint finite-stage scalar convention
(blueprint: def-weil-pbc-qbar-category). -/
instance intrinsicQbarStageLinear (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    Linear E.val (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) where
  homModule K L := Module.compHom (K ⟶ L) (intrinsicQbarStageFieldEquiv.{u} l Ω E).symm.toRingHom
  smul_comp K L M a f g :=
    Linear.smul_comp K L M ((intrinsicQbarStageFieldEquiv.{u} l Ω E).symm a) f g
  comp_smul K L M f a g :=
    Linear.comp_smul K L M f ((intrinsicQbarStageFieldEquiv.{u} l Ω E).symm a) g

private theorem rationalScalar_map_smul
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (K M : sfRationalConstructibleCategory l E Y)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (f : K ⟶ M) :
    (sfRationalScalarExtension l E Y 0 (Fact.out : l.Prime).ne_zero L ι).map (a • f) =
      (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a)) •
        (sfRationalScalarExtension l E Y 0 (Fact.out : l.Prime).ne_zero L ι).map f := by
  let F := sfRationalScalarExtension l E Y 0 (Fact.out : l.Prime).ne_zero L ι
  let I := sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero E L ι Y
  have hs := (sfRationalScalarExtension_existsUnique l E Y 0
    (Fact.out : l.Prime).ne_zero L ι).exists.choose_spec
  let : F.Additive := hs.1
  have hobj (N : sfRationalConstructibleCategory l E Y) : F.obj N = ⟨I.obj N.obj⟩ :=
    hs.2.1 N
  have hm (b : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (g : K.obj ⟶ M.obj) :
      F.map (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] g) = eqToHom (hobj K) ≫
        ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E b))
          ⊗ₜ[Padic.coefficientExtensionIntegers l L] I.map g) ≫ eqToHom (hobj M).symm :=
    (conj_eqToHom_iff_heq _ _ (hobj K) (hobj M)).2 (hs.2.2 K.obj M.obj g b)
  have hc (s : Localization.Away (Padic.coefficientExtensionUniformizer l L))
      (g : (⟨I.obj K.obj⟩ : sfRationalConstructibleCategory l L Y) ⟶ ⟨I.obj M.obj⟩) :
      eqToHom (hobj K) ≫ (s • g) ≫ eqToHom (hobj M).symm =
        s • (eqToHom (hobj K) ≫ g ≫ eqToHom (hobj M).symm) := by
    rw [Linear.smul_comp, Linear.comp_smul]
  change F.map (a • f) = _ • F.map f
  induction f using TensorProduct.inductionOn with
  | tmul b g =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, hm, hm]
    simp only [map_mul]
    rw [← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact hc _ _
  | add f g hf hg =>
    change F.map (a • (f + g)) = _ • F.map (f + g)
    simp only [smul_add, F.map_add, hf, hg]

/-- The literal intrinsic tensor transitions respect the actual coefficient inclusions.
Source: blueprint scalar-action paragraph
(blueprint: def-weil-pbc-qbar-category).
Proof: on integral tensors, extension carries multiplication by a constant to
multiplication by its coefficient-inclusion image. Inverting the uniformizer
preserves the equality. The integral-normalized coefficient equivalence and
Shrink equivalence identify that map with the actual intermediate-field inclusion.
The prescribed associators and the identity transition normalization are linear,
so the same equation holds for the recorded stage system. -/
theorem intrinsicQbarScalarCompatible :
    StageSystem.QbarScalarCompatible l Ω
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y) := by
  intro E L h K M a f
  have hT := (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Y).exists
    |>.choose_spec.1 E L h
  rw [hT]
  change (sfRationalScalarExtension l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y 0
      (Fact.out : l.Prime).ne_zero
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)).map
        ((intrinsicQbarStageFieldEquiv.{u} l Ω E).symm a • f) =
    (intrinsicQbarStageFieldEquiv.{u} l Ω L).symm (IntermediateField.inclusion h a) • _
  rw [rationalScalar_map_smul]
  congr 1
  simp [intrinsicQbarStageFieldEquiv, AlgebraicallyClosedCoefficients.coefficientInclusion]

/-- Multiply the representative after adjoining its scalar to the finite stage.
This is the existing quotient construction, applied to the intrinsic stage system.
Source: blueprint formula alpha [M,u] = [N,alpha u_N]
(blueprint: def-weil-pbc-qbar-category). -/
def intrinsicQbarScalarAction (α : Ω)
    {K L : generalAlgebraicallyClosedConstructibleCategory l Ω Y} (f : K ⟶ L) : K ⟶ L :=
  StageSystem.qbarScalarHom l Ω (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y)
    (intrinsicQbarScalarCompatible l Ω Y) α f

set_option linter.unusedVariables false in
/-- The specified scalar formula determines the linear structure uniquely, on the
existing colimit abelian-group structures. Source: blueprint scalar-action laws
(blueprint: def-weil-pbc-qbar-category).
Proof: represent each finite list of arrows and scalars at one common finite field.
The displayed action is multiplication there. Its one, product, zero and additive
laws are the finite-stage module laws. Bilinearity of composition is the finite-stage
linearity law. The actual Hom-colimit coordinate equivalence identifies sums with
these representative sums, so all laws descend to the existing abelian groups.
This constructs the linear structure. The formula fixes every scalar multiplication;
all remaining module and linearity fields are propositions, proving uniqueness. -/
theorem intrinsicQbarLinear_existsUnique :
    ∃! q : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω Y),
      (fun [qInst : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω Y)] ↦
        ∀ (K L : generalAlgebraicallyClosedConstructibleCategory l Ω Y) (α : Ω) (f : K ⟶ L),
          α • f = intrinsicQbarScalarAction l Ω Y α f) (qInst := q) := by
  have hp : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).pairPreadditive =
      GeneralAlgebraicallyClosedCoefficients.preadditive (l := l) (Ω := Ω) (Y := Y) := by
    exact Subsingleton.elim _ _
  have laws := StageSystem.qbarScalarHom_laws l Ω
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y)
    (intrinsicQbarScalarCompatible l Ω Y)
  rw [hp] at laws
  let q : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω Y) := {
    homModule K L :=
      { smul := fun α f ↦ intrinsicQbarScalarAction l Ω Y α f
        one_smul := laws.1 K L
        mul_smul := laws.2.1 K L
        smul_zero := laws.2.2.1 K L
        smul_add := laws.2.2.2.1 K L
        add_smul := laws.2.2.2.2.1 K L
        zero_smul := laws.2.2.2.2.2.1 K L }
    smul_comp K L M := laws.2.2.2.2.2.2.1 K L M
    comp_smul K L M f α g := laws.2.2.2.2.2.2.2 K L M α f g
  }
  refine ⟨q, ?_, ?_⟩
  · intro K L α f
    rfl
  · intro q' hq'
    have hm : q'.homModule = q.homModule := by
      funext K L
      apply Module.ext
      funext α f
      exact hq' K L α f
    have hext : ∀ (a b : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω Y)),
        a.homModule = b.homModule → a = b := by
      intro a b
      cases a
      cases b
      intro h
      cases h
      rfl
    exact hext q' q hm

/-- The scalar action is fixed on every morphism class, not chosen from mere existence.
The inherited category and triangulation remain literally the recorded pair construction.
Source: blueprint Qbar-linear category (blueprint: def-weil-pbc-qbar-category). -/
instance intrinsicQbarLinear : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  (intrinsicQbarLinear_existsUnique l Ω Y).exists.choose

end WeilConjectures
