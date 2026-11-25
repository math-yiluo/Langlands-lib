/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra

/-!
# The finite coefficient setting for purity

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-conventions.md
(blueprint: def-pur-conventions).

The fixed field datum, coefficient closure, finite subextension and positive level are
bundled together. The coefficient ring is the existing quotient construction, not new data.
The small pro-etale site retains its object universe u+1 and morphism universe u.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

/-- The finite-level purity setting. The field and coefficient data are the published
constructions of def-weil-finite-field-fiber; E is literally a finite subextension of
its fixed coefficient closure. Source: blueprint sk-def-purity-conv,
def-pur-conventions (blueprint: def-pur-conventions). -/
structure PurityFiniteSetting where
  field : FiniteFieldDatum.{u}
  coefficients : field.CoefficientDatum
  extension : IntermediateField (Padic coefficients.l) coefficients.Qbar
  [finiteExtension : FiniteDimensional (Padic coefficients.l) extension]
  level : ℕ
  level_pos : 1 ≤ level

attribute [instance] PurityFiniteSetting.finiteExtension

namespace PurityFiniteSetting

/-- The coefficient ring in the conventions is the existing quotient O_E/(varpi_E^n).
Source: blueprint sk-def-purity-conv, finite coefficient notation
(blueprint: def-pur-conventions). -/
noncomputable def Ring (P : PurityFiniteSetting.{u}) : Type u :=
  Padic.coefficientExtensionRing P.coefficients.l P.extension P.level

/-- The ordinary commutative ring structure on the existing finite coefficient quotient.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable instance ringCommRing (P : PurityFiniteSetting.{u}) : CommRing P.Ring :=
  inferInstanceAs (CommRing
    (Padic.coefficientExtensionRing P.coefficients.l P.extension P.level))

/-- The ramification index is the order of ell in the DVR with uniformizer varpi_E.
Source: blueprint sk-def-purity-conv and lem-pur-finite-kummer-level
(blueprint: def-pur-conventions). -/
noncomputable def ramificationIndex (P : PurityFiniteSetting.{u}) : ℕ :=
  (emultiplicity (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension)
    (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension)).toNat

/-- When e divides n, N=n/e is the finite Kummer level of the affine-line datum.
Source: blueprint sk-prop-a1-kummer, def-pur-affine-line-datum
(blueprint: def-pur-conventions). -/
noncomputable def kummerLevel (P : PurityFiniteSetting.{u}) : ℕ :=
  P.level / P.ramificationIndex

/-- The standard size lift of A for sheaves on the small site. Source: blueprint
sk-def-purity-conv, coefficient-size convention (blueprint: def-pur-conventions). -/
noncomputable def Coefficient (P : PurityFiniteSetting.{u}) : Type (u + 1) :=
  ULift.{u + 1} P.Ring

/-- The coefficient ring structure, cached once for all coefficient sheaf constructions.
This is the ordinary ULift structure on the existing quotient, with no new ring data.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable instance coefficientCommRing (P : PurityFiniteSetting.{u}) :
    CommRing P.Coefficient := inferInstanceAs (CommRing (ULift.{u + 1} P.Ring))

/-- The required finite Kummer exponent. Source: blueprint def-pur-affine-line-datum,
finite-level paragraph (blueprint: def-pur-conventions). -/
noncomputable def exponent (P : PurityFiniteSetting.{u}) : ℕ :=
  P.coefficients.l ^ P.kummerLevel

/-- The divisibility hypothesis makes the exponent kill the coefficient quotient.
Source: blueprint def-pur-affine-line-datum, finite-level paragraph
(blueprint: def-pur-conventions).
Proof: In the DVR O_E the order of ell is e, so ell is a unit times varpi^e.
If e divides n, raising to n/e identifies (ell^(n/e)) with (varpi^n).
The image of ell^(n/e) in the quotient O_E/(varpi^n), and hence in its ULift, is zero. -/
theorem exponent_coefficient_eq_zero (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) : (P.exponent : P.Coefficient) = 0 := by
  apply ULift.down_injective
  change (P.exponent : P.Ring) = 0
  change ((P.coefficients.l ^ P.kummerLevel : ℕ) :
    Padic.coefficientExtensionIntegers P.coefficients.l P.extension ⧸
      Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level) = 0
  rw [← map_natCast (Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)),
    Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  change (P.coefficients.l : Padic.coefficientExtensionIntegers
    P.coefficients.l P.extension) ^ P.kummerLevel ∈
      Ideal.span {Padic.coefficientExtensionUniformizer P.coefficients.l P.extension} ^
        P.level
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hd : Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^
      P.ramificationIndex ∣ (P.coefficients.l : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension) :=
    pow_dvd_of_le_emultiplicity (ENat.natCast_toNat_le_self _)
  simpa only [← pow_mul, kummerLevel, Nat.mul_div_cancel' h] using
    pow_dvd_pow_of_dvd hd P.kummerLevel

/-- Constant finite module coefficients on the etale site. Source: blueprint
sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def constantEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).obj
    (ModuleCat.of P.Coefficient P.Coefficient)

/-- The actual finite root line with extended coefficients. Source: blueprint
sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def twistEtale (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient P.exponent T
    (P.exponent_coefficient_eq_zero h) 1

/-- The scalar-forgetting functor used only to specify the actual Kummer class.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def forgetEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})

/-- Additivity of scalar forgetting. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: addition of sheaf morphisms and forgetting scalars are computed sectionwise. -/
theorem forgetEtale_additive (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (P.forgetEtale T).Additive := by
  constructor
  intro X Y f g
  ext U
  rfl

attribute [instance] forgetEtale_additive

/-- Exactness of scalar forgetting. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: the forgetful functor is both adjoints via extension, restriction and coextension
along Z to A. Sheafification transports these adjunctions. It therefore preserves finite
limits and finite colimits, as in moduleSheafForgetIsLeftAdjoint. -/
theorem forgetEtale_preservesFiniteColimits (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    PreservesFiniteColimits (P.forgetEtale T) := by
  have : (P.forgetEtale T).IsLeftAdjoint :=
    (Sheaf.forget₂CoinduceAdj T.smallEtaleTopology P.Coefficient).isLeftAdjoint
  infer_instance

attribute [instance] forgetEtale_preservesFiniteColimits

/-- Left exactness of scalar forgetting. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: forgetting is a right adjoint, and the sheaf functor inherits its adjunction. -/
theorem forgetEtale_preservesFiniteLimits (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    PreservesFiniteLimits (P.forgetEtale T) := by
  let U := forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}
  have : U.IsRightAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom P.Coefficient) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsRightAdjoint
    have : (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom P.Coefficient)).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom P.Coefficient)).isRightAdjoint
    infer_instance
  have : (sheafCompose T.smallEtaleTopology U).IsRightAdjoint := inferInstance
  exact inferInstanceAs (PreservesFiniteLimits (sheafCompose T.smallEtaleTopology U))

attribute [instance] forgetEtale_preservesFiniteLimits

/-- Scalar forgetting commutes with sheafification. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: the coefficient forgetful functor preserves finite limits and all colimits,
using both scalar adjunctions. The sheafification comparison is consequently invertible. -/
theorem forget_preservesSheafification (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) := by
  let U := forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom P.Coefficient) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
    have : (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom P.Coefficient)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom P.Coefficient)).isLeftAdjoint
    infer_instance
  exact Sheaf.preservesSheafification_of_adjunction T.smallEtaleTopology
    (Adjunction.ofIsLeftAdjoint U)

attribute [instance] forget_preservesSheafification

/-- The comparison's degree-zero free-generator map, Z to the underlying constant A.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def integerToConstant (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (P.forgetEtale T).obj (P.constantEtale T) :=
  (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((AddCommGrpCat.uliftZMultiplesAddEquiv (AddCommGrpCat.of P.Coefficient)).symm 1) ≫
    (constantCommuteCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).inv.app
        (ModuleCat.of P.Coefficient P.Coefficient)

/-- The canonical map from module cohomology to the underlying abelian Ext group.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def moduleClassToAbelian (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (x : Abelian.Ext (P.constantEtale T) F 1) :
    Sheaf.H ((P.forgetEtale T).obj F) 1 :=
  (Abelian.Ext.mk₀ (P.integerToConstant T)).comp
    (x.mapExactFunctor (P.forgetEtale T)) (zero_add 1)

set_option backward.isDefEq.respectTransparency false in
private theorem integerToConstant_hom_bijective (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    Function.Bijective (fun f : P.constantEtale T ⟶ F ↦
      P.integerToConstant T ≫ (P.forgetEtale T).map f) := by
  let J := T.smallEtaleTopology
  let U := forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}
  let A := ModuleCat.of P.Coefficient P.Coefficient
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let t := terminal T.Etale
  let h := terminalIsTerminal (C := T.Etale)
  let am := constantSheafAdj J (ModuleCat.{u + 1} P.Coefficient) h
  let ab := constantSheafAdj J AddCommGrpCat.{u + 1} h
  let i : Z ⟶ U.obj A :=
    (AddCommGrpCat.uliftZMultiplesAddEquiv (AddCommGrpCat.of P.Coefficient)).symm 1
  let e : (A ⟶ F.obj.obj (op t)) ≃ (Z ⟶ U.obj (F.obj.obj (op t))) :=
    ModuleCat.homEquiv.trans
      ((LinearMap.ringLmapEquivSelf P.Coefficient ℤ _).toEquiv.trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv
          (AddCommGrpCat.of (F.obj.obj (op t)))).symm.toEquiv)
  have he (g : A ⟶ F.obj.obj (op t)) : e g = i ≫ U.map g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    change n.down • g.hom 1 = g.hom (n.down • (1 : P.Coefficient))
    exact (map_zsmul g.hom _ _).symm
  let e' := ((am.homEquiv A F).trans e).trans
    (ab.homEquiv Z ((P.forgetEtale T).obj F)).symm
  convert e'.bijective using 1
  funext f
  dsimp only [e', Equiv.trans_apply]
  erw [he, Adjunction.homEquiv_counit]
  have hf := (am.homEquiv A F).symm_apply_apply f
  rw [Adjunction.homEquiv_counit] at hf
  conv_lhs => rw [← hf]
  simp only [integerToConstant, Functor.map_comp, Category.assoc]
  change (constantSheaf J AddCommGrpCat.{u + 1}).map i ≫
      (constantCommuteCompose J U).inv.app A ≫
      (sheafCompose J U).map
        ((constantSheaf J (ModuleCat.{u + 1} P.Coefficient)).map (am.homEquiv A F f)) ≫
      (sheafCompose J U).map (am.counit.app F) = _
  erw [← (constantCommuteCompose J U).inv.naturality_assoc]
  erw [← constantSheafAdj_counit_w J U F h]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

private theorem forgetEtale_H_one_subsingleton (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    [Injective F] : Subsingleton (Sheaf.H ((P.forgetEtale T).obj F) 1) := by
  let J := T.smallEtaleTopology
  let e := Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{u + 1}
    (terminalIsTerminal (C := T.Etale))
  have : ((sheafSections J AddCommGrpCat.{u + 1}).obj
      (op (terminal T.Etale))).Additive := Functor.additive_of_iso e
  apply (Sheaf.subsingleton_H_iff_isZero_rightDerived J
    (terminalIsTerminal (C := T.Etale)) 1 _).mpr
  exact (Scheme.isZero_rightDerived_globalSections_forget_of_injective
    T P.Coefficient F 0).of_iso ((NatIso.rightDerived e 1).app _).symm

/-- This comparison is bijective, so it selects no arbitrary cohomology class.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions).
Proof: Hom_A(A,-) is global sections. Forgetting an injective module sheaf is acyclic
for abelian global sections. Apply the natural acyclic-resolution comparison, whose
map in degree zero is precisely precomposition by Z to A. It is bijective in degree one. -/
theorem moduleClassToAbelian_bijective (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    Function.Bijective (P.moduleClassToAbelian T F) := by
  let U := P.forgetEtale T
  let X := P.constantEtale T
  let Z := (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let c (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) (n : ℕ) :=
    ((Abelian.Ext.mk₀ (P.integerToConstant T)).precomp (U.obj G) (zero_add n)).comp
      (U.mapExtAddHom X G n)
  have hc (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
      Function.Bijective (c G 0) := by
    convert ((Abelian.Ext.mk₀_bijective _ _).comp
      ((integerToConstant_hom_bijective P T G).comp
        (Abelian.Ext.addEquiv₀ (X := X) (Y := G)).bijective)) using 1
    funext x
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective X G).surjective x
    change (Abelian.Ext.mk₀ (P.integerToConstant T)).comp
      ((Abelian.Ext.mk₀ f).mapExactFunctor U) (zero_add 0) = _
    simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀,
      Function.comp_apply]
    congr 2
    exact congrArg U.map ((Abelian.Ext.addEquiv₀ (X := X) (Y := G)).apply_symm_apply f).symm
  let I : InjectivePresentation F := Classical.arbitrary _
  let S := ShortComplex.mk _ _ (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have : Injective S.X₂ := I.injective
  have : Subsingleton (Abelian.Ext Z (U.obj S.X₂) 1) :=
    forgetEtale_H_one_subsingleton P T S.X₂
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
    ((Abelian.Ext.mk₀ S.g).postcomp X (add_zero 0))
    (hS.extClass.postcomp X (show 0 + 1 = 1 from rfl))
    ((Abelian.Ext.mk₀ (U.map S.g)).postcomp Z (add_zero 0))
    ((hS.map U).extClass.postcomp Z (show 0 + 1 = 1 from rfl))
    (c S.X₂ 0) (c S.X₃ 0) (c S.X₁ 1)
    (by
      apply AddMonoidHom.ext
      intro x
      change ((Abelian.Ext.mk₀ (P.integerToConstant T)).comp
        (x.mapExactFunctor U) (zero_add 0)).comp
          (Abelian.Ext.mk₀ (U.map S.g)) (add_zero 0) =
        (Abelian.Ext.mk₀ (P.integerToConstant T)).comp
          ((x.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)).mapExactFunctor U) (zero_add 0)
      rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
      exact Abelian.Ext.comp_assoc _ _ _ rfl rfl rfl)
    (by
      apply AddMonoidHom.ext
      intro x
      change ((Abelian.Ext.mk₀ (P.integerToConstant T)).comp
        (x.mapExactFunctor U) (zero_add 0)).comp (hS.map U).extClass rfl =
        (Abelian.Ext.mk₀ (P.integerToConstant T)).comp
          ((x.comp hS.extClass rfl).mapExactFunctor U) (zero_add 1)
      rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
      exact Abelian.Ext.comp_assoc _ _ _ rfl rfl rfl)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Abelian.Ext.covariant_sequence_exact₃' X hS 0 1 rfl))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Abelian.Ext.covariant_sequence_exact₃' Z (hS.map U) 0 1 rfl))
    (hc _).surjective (hc _)
    (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ X hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl)
    (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ Z (hS.map U) x
      (by change (Abelian.Ext.mk₀ (U.map S.f)).postcomp Z (zero_add 1) x = 0
          exact (inferInstance : Subsingleton (Abelian.Ext Z (U.obj S.X₂) 1)).elim _ _)
      rfl)

/-- Constant pro-etale coefficients, via the canonical comparison inverse image.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def constant (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj (P.constantEtale T)

/-- The finite pro-etale twist, via the canonical comparison inverse image.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def twist (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj (P.twistEtale h T)

/-- Either of the two actual coefficient sheaves used in the proposition.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def coefficientSheaf (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) (twisted : Bool) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  if twisted then P.twist h T else P.constant T

/-- The actual degree-zero object of the unbounded derived category.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def derivedSheaf (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) (twisted : Bool) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.coefficientSheaf h T twisted)

private theorem coefficientPrime_isUnit_field (P : PurityFiniteSetting.{u}) :
    IsUnit (P.coefficients.l : P.field.k) := by
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
  have : CharP P.field.k P.field.p :=
    charP_of_injective_algebraMap' P.field.k₀ P.field.p
  exact isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime _
    (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)

private theorem coefficientPrime_isUnit_sections (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (CommRingCat.of P.field.k)) :
    IsUnit (P.coefficients.l : Γ(T, ⊤)) := by
  let f := (Scheme.ΓSpecIso (CommRingCat.of P.field.k)).inv ≫ a.appTop
  simpa only [map_natCast] using (coefficientPrime_isUnit_field P).map f.hom

/-- Invertibility of the Kummer exponent on any k-scheme, without a finite-type
restriction. Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions).
Proof: the fixed field has characteristic p and ell differs from p, so ell, hence every
power of ell, is a unit in k. Its image along the structure morphism is a unit. -/
theorem exponent_isUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (CommRingCat.of P.field.k)) : IsUnit (P.exponent : Γ(T, ⊤)) := by
  simpa only [exponent, Nat.cast_pow] using
    (coefficientPrime_isUnit_sections P T a).pow P.kummerLevel

/-- The coefficient prime is invertible in every local ring of a scheme over the fixed
algebraically closed finite-field base.
Source: blueprint def-pur-conventions, ell distinct from the characteristic
(blueprint: def-pur-conventions).
Proof: k_0 has cardinality p^a with p prime and a positive, hence characteristic p.
Its algebraic closure k has the same characteristic. The prime ell differs from p,
so its image is a nonzero element of the field k and therefore a unit. The structure
map induces k to the local ring at x, preserving units and the scalar ell. -/
theorem coefficientPrime_isUnit_stalk (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (CommRingCat.of P.field.k)) (x : T) :
    IsUnit (P.coefficients.l : T.presheaf.stalk x) := by
  simpa only [map_natCast] using (coefficientPrime_isUnit_sections P T a).map
    (T.presheaf.germ ⊤ x (by trivial)).hom

end PurityFiniteSetting
end WeilConjectures
