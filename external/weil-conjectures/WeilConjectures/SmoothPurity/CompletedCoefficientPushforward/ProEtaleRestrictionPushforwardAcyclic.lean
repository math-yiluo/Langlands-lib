/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import WeilConjectures.CategoryTheory.SiteRestrictionKInjective
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.SiteModuleExtensionByZeroExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

/-! # Restricted K-injectives are acyclic for pro-etale direct image

Source: Stacks Project, Cohomology on Sites, Tag 0D6E,
lemma-derived-pushforward-composition.
(blueprint: lem-pur-proetale-restriction-pushforward-acyclic).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules
namespace WeilConjectures.CompletedCoefficientPushforward

private theorem sliceAbSheafify (X : Scheme.{t}) (U : X.ProEt) :
    HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{max u (t + 1)} := by
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  exact hasSheafifyEssentiallySmallSite _ _

private theorem sliceAbLocallyBijective (X : Scheme.{t}) (U : X.ProEt) :
    ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} := by
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

private theorem commRingSheaf
    {T : Type v} [Category.{w} T] {J : GrothendieckTopology T}
    (B : Sheaf J RingCat.{max u v w})
    (hB : ∀ (U : Tᵒᵖ) (a b : B.obj.obj U), a * b = b * a) :
    ∃ O : Sheaf J CommRingCat.{max u v w},
      (sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj O = B := by
  let obj (U : Tᵒᵖ) : CommRingCat.{max u v w} :=
    { carrier := B.obj.obj U
      commRing := { (inferInstance : Ring (B.obj.obj U)) with mul_comm := hB U } }
  let Oc : Tᵒᵖ ⥤ CommRingCat.{max u v w} :=
    { obj := obj
      map := fun {U V} g ↦
        @CommRingCat.ofHom (obj U) (obj V) (obj U).commRing (obj V).commRing
          (B.obj.map g).hom
      map_id := fun U ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (B.obj.map_id U)
      map_comp := fun g h ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (B.obj.map_comp g h) }
  have hO : Presheaf.IsSheaf J Oc := by
    apply Presheaf.isSheaf_of_isSheaf_comp J Oc (forget₂ CommRingCat RingCat)
    exact B.property
  exact ⟨⟨Oc, hO⟩, rfl⟩

private theorem quasiIso_of_sections {X : Scheme.{t}}
    {B : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {K L : CochainComplex (Mod X B) ℤ} (f : K ⟶ L)
    (h : ∀ U : X.ProEtᵒᵖ, QuasiIso (((SheafOfModules.toSheaf B ⋙
      sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} ⋙
      (CategoryTheory.evaluation _ _).obj U).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  apply CategoryTheory.quasiIso_of_sectionsOfUniverses.{t + 1, t, u} f
  intro U
  exact h (op U)

private theorem restrictionEvaluation_quasiIso {X : Scheme.{t}}
    {B C : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}} (a : B ⟶ C)
    (I : CochainComplex (Mod X
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj C)) ℤ)
    (K : CochainComplex (Mod X
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B)) ℤ)
    (j : ((SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map a)).mapHomologicalComplex
        (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso j] (U : X.ProEt) :
    QuasiIso (((SheafOfModules.toSheaf _ ⋙
      sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} ⋙
      (CategoryTheory.evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map j) := by
  let := integralCoefficientAbSheafify.{t, u} X
  let := integralCoefficientAbLocallyBijective.{t, u} X
  let : HasSheafify ((ProEt.topology X).over U) AddCommGrpCat.{max u (t + 1)} :=
    sliceAbSheafify.{t, u} X U
  let : ((ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := sliceAbLocallyBijective.{t, u} X U
  let BR := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B
  let CR := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj C
  let b := (ProEt.topology X).overPullback CommRingCat.{max u (t + 1)} U
  let B' := b.obj B
  let C' := b.obj C
  let a' := b.map a
  let resB := SheafOfModules.overFunctor.{max u (t + 1)} BR U
  let resC := SheafOfModules.overFunctor.{max u (t + 1)} CR U
  have : resB.Additive := localizedSystemRestrictionAdditive.{t + 1, t, max u (t + 1)} B U
  have : resC.Additive := localizedSystemRestrictionAdditive.{t + 1, t, max u (t + 1)} C U
  let : Abelian (Mod X BR) := modAbelian.{t, u} X BR
  let : Abelian (Mod X CR) := modAbelian.{t, u} X CR
  let : Abelian (SheafOfModules.{max u (t + 1)} (BR.over U)) := inferInstance
  let : Abelian (SheafOfModules.{max u (t + 1)} (CR.over U)) := inferInstance
  have hB := SheafOfModules.overFunctor_exact_ofUniverses.{t + 1, t, max u (t + 1)} BR U
  have := hB.1
  have := hB.2
  have : resB.PreservesKInjectiveComplexes :=
    overFunctor_preservesKInjectiveComplexes_ofUniverses.{t + 1, t, max u (t + 1)} BR U
  have : resC.PreservesKInjectiveComplexes :=
    overFunctor_preservesKInjectiveComplexes_ofUniverses.{t + 1, t, max u (t + 1)} CR U
  let forgetSlice := sheafCompose ((ProEt.topology X).over U)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let I' : CochainComplex (SheafOfModules.{max u (t + 1)} (forgetSlice.obj C')) ℤ :=
    (resC.mapHomologicalComplex (.up ℤ)).obj I
  let K' : CochainComplex (SheafOfModules.{max u (t + 1)} (forgetSlice.obj B')) ℤ :=
    (resB.mapHomologicalComplex (.up ℤ)).obj K
  let j' : ((SheafOfModules.restrictScalars (forgetSlice.map a')).mapHomologicalComplex
      (.up ℤ)).obj I' ⟶ K' := (resB.mapHomologicalComplex (.up ℤ)).map j
  have : CochainComplex.IsKInjective I' :=
    inferInstanceAs (CochainComplex.IsKInjective
      ((resC.mapHomologicalComplex (.up ℤ)).obj I))
  have : CochainComplex.IsKInjective K' :=
    inferInstanceAs (CochainComplex.IsKInjective
      ((resB.mapHomologicalComplex (.up ℤ)).obj K))
  have : QuasiIso j' :=
    inferInstanceAs (QuasiIso ((resB.mapHomologicalComplex (.up ℤ)).map j))
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  have hq := coefficientRestrictionSections_quasiIso.{t + 1, t, max u (t + 1)}
    (J := (ProEt.topology X).over U)
    (R := B') (S := C') a' I' K' j'
  let Γ := SheafOfModules.toSheaf (BR.over U) ⋙
    sheafToPresheaf ((ProEt.topology X).over U) AddCommGrpCat.{max u (t + 1)} ⋙ lim
  let ev := SheafOfModules.toSheaf (BR.over U) ⋙
    (sheafSections ((ProEt.topology X).over U) AddCommGrpCat.{max u (t + 1)}).obj
      (op (Over.mk (𝟙 U)))
  let e : Γ ≅ ev := Functor.isoWhiskerLeft (SheafOfModules.toSheaf (BR.over U))
    ((Sheaf.ΓNatIsoLim _ _).symm ≪≫ Sheaf.ΓNatIsoSheafSections _ _ Over.mkIdTerminal)
  have ht : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map j') :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex e (.up ℤ)) (Arrow.mk j'))).mp hq
  exact ht

/-- Restricting a K-injective complex along a commutative coefficient map produces
an acyclic complex for the direct image of a scheme morphism. The assertion is for
any supplied universal right-derived model and does not assert that scalar restriction
preserves K-injectives.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E,
lemma-derived-pushforward-composition, applied to a coefficient change followed by f.
(blueprint: lem-pur-proetale-restriction-pushforward-acyclic).

Proof: choose a K-injective resolution j of the scalar restriction of I. Restriction
of I and of the resolution to every slice X/U remains K-injective, and exactness of
slice restriction preserves the quasi-isomorphism j. Apply scalar-restriction acyclicity
for global sections on X/U. Sections on X/U are evaluation on its terminal object,
so j is a quasi-isomorphism on sections over each U. Direct image evaluates these
same section complexes over the base changes of objects of Y. Sectionwise detection
therefore makes f_*(j) a quasi-isomorphism of module-sheaf complexes. The unit of the
supplied derived model is invertible on the K-injective resolution. Its naturality
square at j, together with the invertibility of Q(j) and Q(f_*(j)), proves that its
unit on the restricted I is invertible. No flatness or commutativity of the target
coefficient ring is used. Zero rings and identity coefficient maps are included. -/
theorem restrictionPushforward_acyclic {X Y : Scheme.{t}} (f : X ⟶ Y)
    {B C : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}}
    {D : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (hB : ∀ (U : X.ProEtᵒᵖ) (a b : B.obj.obj U), a * b = b * a)
    (hC : ∀ (U : X.ProEtᵒᵖ) (a b : C.obj.obj U), a * b = b * a)
    (a : B ⟶ C) (c : D ⟶ (ringPush.{t, u} f).obj B)
    [(push f c).Additive] (F : RightImage (push f c))
    (I : CochainComplex (Mod X C) ℤ) (hI : I.IsKInjective) :
    IsIso (F.unit.app
      (((SheafOfModules.restrictScalars.{max u (t + 1)} a).mapHomologicalComplex
        (.up ℤ)).obj I)) := by
  classical
  have := hI
  obtain ⟨B', rfl⟩ := commRingSheaf.{u, t + 1, t} B hB
  obtain ⟨C', rfl⟩ := commRingSheaf.{u, t + 1, t} C hC
  have : IsGrothendieckAbelian.{max u (t + 1)}
      (Mod X ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj B')) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      (ProEt.topology X) B').1
  let forgetR := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let a' : B' ⟶ C' := forgetR.preimage a
  have ha : forgetR.map a' = a := Functor.map_preimage forgetR a
  rw [← ha]
  let L := ((SheafOfModules.restrictScalars (forgetR.map a')).mapHomologicalComplex
    (.up ℤ)).obj I
  obtain ⟨K, hK, j, hj, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective L
  have := hq
  have hpush : QuasiIso (((push f c).mapHomologicalComplex (.up ℤ)).map j) := by
    apply quasiIso_of_sections.{t, u}
    intro U
    exact restrictionEvaluation_quasiIso a' I K j ((proEtaleBaseChange f).obj U.unop)
  have := F.computes K hK
  have hn := F.unit.naturality j
  dsimp only [Functor.comp_map] at hn
  have hi : IsIso (F.unit.app L ≫ F.functor.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.functor.map (DerivedCategory.Q.map j))

end WeilConjectures.CompletedCoefficientPushforward
