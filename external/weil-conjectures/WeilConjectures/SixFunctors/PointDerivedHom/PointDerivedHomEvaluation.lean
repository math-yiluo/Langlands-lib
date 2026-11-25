/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PointDerivedHom.PointDerivedHomModels
import WeilConjectures.SixFunctors.PointDerivedHom.PointExtensionKFlat
import WeilConjectures.SixFunctors.PointDerivedHom.PointHomComplexAdjunction
import WeilConjectures.SixFunctors.PointDerivedHom.PointTensorHomEvaluation
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.HomComplexComponents

set_option linter.privateModule false

/-! # Derived Hom and evaluation at a pro-etale point

Source: Stacks Project, Tags 0A8X, 08J7, 08BJ and 0G7E.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

private theorem generator_one_natural
    (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    (α : constantRing.{t, u} k R ⟶ B)
    (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (hobj : ∀ M : ModuleCat.{max u (t + 1)} R, L.obj M = extensionObject k B α M)
    (adj : L ⊣ sections.{t, u} k B α)
    (hex : ExplicitAdjunction k B α L hobj adj)
    {M N : ModuleCat.{max u (t + 1)} R} (f : M ⟶ N) (x : M) :
    (L.map f).val.app (op (finalObject k))
      (generator k B α L hobj M (op (finalObject k)) 1 x) =
        generator k B α L hobj N (op (finalObject k)) 1 (f.hom x) := by
  have hu (T : ModuleCat.{max u (t + 1)} R) (y : T) :
      (adj.unit.app T).hom y = generator k B α L hobj T (op (finalObject k)) 1 y := by
    have h := hex.1 T (L.obj T) (𝟙 _) y
    rw [adj.homEquiv_id] at h
    exact h
  have h := congrArg (fun a ↦ a.hom x) (adj.unit.naturality f)
  change (adj.unit.app N).hom (f.hom x) =
    (L.map f).val.app (op (finalObject k)) ((adj.unit.app M).hom x) at h
  rw [hu, hu] at h
  exact h.symm

private theorem homValue_natural
    (k : Type t) [Field k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    {P P' I I' : CochainComplex (Modules.{t, u} k B) ℤ}
    (f : P' ⟶ P) (g : I ⟶ I') (j p : ℤ)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (h : ((sheafHom k B P I).X j).val.obj U) (x : (P'.X p).val.obj U) :
    homValue k B P' I' j p U
      (((((homComplexFunctor (R := B)).map f.op).app I ≫
        ((homComplexFunctor (R := B)).obj (op P')).map g).f j).val.app U h) x =
      (g.f (p + j)).val.app U
        (homValue k B P I j p U h ((f.f p).val.app U x)) := by
  have he := homComplexFunctor_map_f_π f g j p (p + j) rfl
  have hx := congrArg (fun a ↦ (((a.val.app U h).app
    (op (Over.mk (𝟙 U.unop)))).hom x)) he
  exact hx

private theorem comparison_natural
    (k : Type t) [Field k] {R : CommRingCat.{max u (t + 1)}}
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
    (α : constantRing.{t, u} k R ⟶ B)
    (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
    (hobj : ∀ M : ModuleCat.{max u (t + 1)} R, L.obj M = extensionObject k B α M)
    (adj : L ⊣ sections.{t, u} k B α)
    (hex : ExplicitAdjunction k B α L hobj adj)
    (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
    (I : CochainComplex (Modules.{t, u} k B) ℤ)
    (q : (sectionComplex k B α).obj
      (sheafHom k B ((extensionComplex k B α L adj).obj c) I) ≅
        CochainComplex.moduleHomComplex c ((sectionComplex k B α).obj I))
    (hq : IsComparison k B α L hobj adj c I q) :
    ComparisonNatural k B α L hobj adj c I q := by
  intro c' I' f g q' hq' j p h x
  rw [hq', hq]
  refine (homValue_natural k B ((extensionComplex k B α L adj).map f) g j p
    (op (finalObject k)) h
    (generator k B α L hobj (c'.X p) (op (finalObject k)) 1 x)).trans ?_
  exact congrArg (fun y ↦ (g.f (p + j)).val.app (op (finalObject k))
    (homValue k B ((extensionComplex k B α L adj).obj c) I j p
      (op (finalObject k)) h y))
    (generator_one_natural k B α L hobj adj hex (f.f p) x)

end WeilConjectures.PointDerivedHom
