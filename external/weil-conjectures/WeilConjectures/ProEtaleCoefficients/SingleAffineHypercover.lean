/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.ProEtaleCoefficients.FormalWContractibleHypercover
import WeilConjectures.ProEtaleCoefficients.FiniteCoproductWContractibleSpectrum
import WeilConjectures.ProEtaleCoefficients.HypercoverSpectrumReplacement
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.RepresentableEpiCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercoverGeometry
import all WeilConjectures.CategoryTheory.SimplicialMatchingObject
import all WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverExistence
import all Mathlib.CategoryTheory.Sites.Precoverage
import all Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import all WeilConjectures.CategoryTheory.ProperFaceMatchingObject
import all WeilConjectures.CategoryTheory.SiteFiniteBasisHypercoverStep
import all WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtension
import all Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import all WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase
import all Mathlib.AlgebraicTopology.SimplicialObject.Basic
import all Mathlib.Basic.Finite.Sigma
import all WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionConstruction
import all WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentComposition
import all WeilConjectures.AlgebraicGeometry.SiteHypercoverAttachmentOperators
import all WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionSplit
import all Mathlib.Basic.Finite.Sum
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import all Mathlib.CategoryTheory.Limits.IsConnected
import all Mathlib.AlgebraicTopology.SimplexCategory.Basic
import all Mathlib.CategoryTheory.Sites.PreservesLimits
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import all WeilConjectures.AlgebraicGeometry.ProEtaleQcAffineContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-! Hypercover existence after the finite-family construction.
(blueprint: det-pe-hypercover-single-affine) -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProEt
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 09A1; Hypercoverings Tags 094K, 0DAV and 0DB2.
(blueprint: det-pe-hypercover-single-affine)

Proof:
1. Apply the finite-basis hypercover theorem to the qcqs subsite, with the basis of
   literal spectra of w-contractible rings. The singleton covering theorem and finite
   adjoining property give its hypotheses. The formal hypercover theorem retains all
   proper-face limiting cones, projection equations and component covering presieves.
2. Realize each finite family by its scheme coproduct, supplied by the qcqs finite-family
   geometry theorem. Its representable-sheaf coproduct mapping property gives the
   augmentation. Define every simplicial operator by the coproduct mapping property;
   verify identities and compositions on the coprojections.
3. Reuse the proved sheaf-realization functor and its finite-limit preservation from
   `ProEtaleAffineAcyclicHypercoverGeometry`. Its comparison lemmas identify the realized
   proper-face maps with the formal matching maps. Componentwise covers become epimorphisms
   after sheaf realization. The degree-zero target is the terminal object over U.
4. Construct the positive-degree proper-face limits in the qcqs slice, and preserve them
   under inclusion into the full slice. Thus the targets are quasi-separated; all sources
   are quasi-compact finite coproducts. Lower the represented epimorphisms from the lifted
   value universe and apply the represented-epi singleton covering criterion. This gives
   actual singleton covers, including in degree zero.
5. Reindex each finite family into the scheme universe and use Mathlib's finite `sigmaSpec`
   isomorphism. The finite-product theorem proves the product ring w-contractible. Replace
   each term by that spectrum using the spectrum replacement theorem. Conjugation preserves
   the simplicial laws, and transport of the cones preserves all matching equations and
   covering assertions. Empty families and the zero ring are included throughout.
-/
theorem exists_single_affine_wContractible_hypercover
    (X : Scheme.{u}) (U : X.ProEt) (hUqc : CompactSpace U.left)
    (hUqs : QuasiSeparatedSpace U.left) :
    ∃ (W : SimplicialObject (Over U)),
      (∀ (r : ℕ),
        ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f),
          IsWContractibleRing D ∧
            (W _⦋r⦌).left = @Scheme.ProEt.mk X _ f hf) ∧
      Presieve.singleton (W _⦋0⦌).hom ∈
        (Scheme.ProEt.precoverage X) U ∧
      (∀ (r : ℕ),
        ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
          (μ : W _⦋r + 1⦌ ⟶ c.pt),
          Nonempty (IsLimit c) ∧
            Presieve.singleton μ.left ∈ (Scheme.ProEt.precoverage X) c.pt.left ∧
            (∀ (a : SimplicialObject.ProperFaceCategory (r + 1)),
              μ ≫ c.π.app (Opposite.op a) = W.map a.obj.hom.op)) := by
  classical
  obtain ⟨T, K, M, μ, hT, hfinite, hbasis, hlim, hproj, hcover⟩ :=
    exists_formal_wContractible_hypercover X U hUqc hUqs
  subst U
  let U := T.obj
  obtain ⟨haffqc, ⟨hpb, J, hJ, hinc, hsch, hcov, hslice, hadjoin⟩, hsub, hcop⟩ :=
    qcqs_finite_family_geometry.{u, u + 1, 0} X
  let := hpb
  have : HasFiniteLimits (Over U) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let G : Over T ⥤ Over U := Over.post (X := T) (qcqsInclusion X)
  have : HasFiniteLimits (Over T) := (hslice T).1
  have : PreservesFiniteLimits G := (hslice T).2.1
  let K' : SimplicialObject (FormalCoproduct.{u + 1} (Over U)) := K ⋙ familyMap G
  let Y := (topology X).uliftYoneda.{u + 1}
  have : PreservesFiniteLimits Y := ⟨fun J _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (Over.post Y (X := U)) := inferInstance
  let : HasPushouts (Sheaf (topology X) (Type (u + 1))) :=
    Sheaf.instHasColimitsOfShape
  let : HasCoproducts.{u + 1} (Sheaf (topology X) (Type (u + 1))) := fun I ↦
    Sheaf.instHasColimitsOfShape
  let : HasCoproducts.{u + 1} (Over (Y.obj U)) :=
    fun I ↦ CategoryTheory.Over.instHasColimitsOfShape
  let R := GeometryRealization.sheafRealization (topology X) U
  have : PreservesFiniteLimits R :=
    GeometryRealization.sheafRealization_preservesFiniteLimits (topology X) U
  have : PreservesFiniteLimits (familyMap G) := familyMap_preservesFiniteLimits G
  let F := familyMap G ⋙ R
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have hcops (n : ℕ) := by
    let := hfinite n
    exact hcop (K _⦋n⦌).I (fun i ↦ ((K _⦋n⦌).obj i).left.obj)
      (fun i ↦ ((K _⦋n⦌).obj i).left.property.1)
      (fun i ↦ ((K _⦋n⦌).obj i).left.property.2)
  choose A ι e he hqc hqs haff hcolim hiso hprod hnat hempty using hcops
  let g (n : ℕ) : A n ⟶ U := Y.preimage
    ((hcolim n).some.desc (Cofan.mk (Y.obj U)
      (fun i ↦ Y.map (G.obj ((K _⦋n⦌).obj i)).hom)))
  have hιg (n : ℕ) (i : (K _⦋n⦌).I) :
      ι n i ≫ g n = (G.obj ((K _⦋n⦌).obj i)).hom := by
    apply Y.map_injective
    simp only [Functor.map_comp, g, Functor.map_preimage]
    exact (hcolim n).some.fac _ ⟨i⟩
  let a (n : ℕ) : Cofan (K' _⦋n⦌).obj :=
    Cofan.mk (Over.mk (g n)) (fun i ↦ Over.homMk (ι n i) (hιg n i))
  have hsa (n : ℕ) : IsColimit (Cofan.mk ((Over.post Y).obj (a n).pt)
      (fun i ↦ (Over.post Y).map ((a n).inj i))) := by
    apply isColimitOfReflects (Over.forget (Y.obj U))
    exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm (hcolim n).some
  have ha (n : ℕ) : IsColimit (a n) := by
    apply isColimitOfReflects (Over.post Y)
    exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm (hsa n)
  let V : SimplicialObject (Over U) :=
    { obj := fun n ↦ (a n.unop.len).pt
      map := fun {n m} φ ↦ (ha n.unop.len).desc
        (Cofan.mk (a m.unop.len).pt
          (fun i ↦ (K'.map φ).φ i ≫ (a m.unop.len).inj ((K'.map φ).f i)))
      map_id := by
        intro n
        apply Cofan.IsColimit.hom_ext (ha n.unop.len)
        intro i
        simp only [Cofan.IsColimit.inj_desc]
        change (K'.map (𝟙 n)).φ i ≫ _ = _
        rw [K'.map_id]
        simp
      map_comp := by
        intro n m l φ ψ
        apply Cofan.IsColimit.hom_ext (ha n.unop.len)
        intro i
        simp only [Cofan.IsColimit.inj_desc]
        change (K'.map (φ ≫ ψ)).φ i ≫ _ = _
        rw [K'.map_comp]
        simp [Category.assoc] }
  let b (n : ℕ) : F.obj (K _⦋n⦌) ≅ (Over.post Y).obj (a n).pt :=
    (coproductIsCoproduct _).coconePointUniqueUpToIso (hsa n)
  have hb (n : ℕ) (i : (K _⦋n⦌).I) :
      Sigma.ι (fun i ↦ (Over.post Y).obj (G.obj ((K _⦋n⦌).obj i))) i ≫
        (b n).hom = (Over.post Y).map ((a n).inj i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
      (hsa n) (Discrete.mk i)
  let eb : K ⋙ F ≅ V ⋙ Over.post Y :=
    NatIso.ofComponents (fun n ↦ b n.unop.len) (by
      intro n m φ
      rcases n with ⟨⟨n⟩⟩
      rcases m with ⟨⟨m⟩⟩
      apply Sigma.hom_ext
      intro i
      simp only [Functor.comp_map, F, R, GeometryRealization.sheafRealization,
        FormalCoproduct.eval_obj_map, Sigma.ι_comp_desc_assoc,
        Function.comp_def, Category.assoc, familyMap]
      rw [hb m]
      rw [← Category.assoc, hb n]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp [V, K', familyMap])
  have hFepi (n : ℕ) : Epi (F.map (μ n)) := by
    apply GeometryRealization.sheafRealization_map_epi (precoverage X)
      ((familyMap G).map (μ n))
    intro j
    have hv := hcov ((M n).pt.obj j).left _ (hcover n j)
    simpa [Presieve.map_ofArrows, G, familyMap, Over.post, eqToHom_map] using hv
  have hterms (n : ℕ) : ∃ D : CommRingCat.{u},
      IsWContractibleRing D ∧ Nonempty (Spec D ≅ (V _⦋n⦌).left.left) := by
    let := hfinite n
    obtain ⟨D, hD, ⟨hd⟩⟩ := finite_coproduct_wContractible_spectrum
      (K _⦋n⦌).I (fun i ↦ ((K _⦋n⦌).obj i).left.obj.left) (by
        intro i
        obtain ⟨D, f, hf, hD, heq⟩ := hbasis n i
        exact ⟨D, hD, ⟨eqToIso (congrArg (fun Q ↦ Q.left) heq).symm⟩⟩)
    exact ⟨D, hD, ⟨hd ≪≫ e n⟩⟩
  have hVqc (n : ℕ) : CompactSpace (V _⦋n⦌).left.left := hqc n
  have hVqs (n : ℕ) : QuasiSeparatedSpace (V _⦋n⦌).left.left := hqs n
  let Vq : SimplicialObject (Over T) :=
    { obj := fun n ↦ Over.mk
        (Y := ⟨(V.obj n).left, hVqc n.unop.len, hVqs n.unop.len⟩)
        (ObjectProperty.homMk (V.obj n).hom)
      map := fun {n m} φ ↦ Over.homMk (ObjectProperty.homMk (V.map φ).left) (by
        apply ObjectProperty.hom_ext
        exact Over.w (V.map φ))
      map_id := by
        intro n
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        exact congrArg (fun f ↦ f.left) (V.map_id n)
      map_comp := by
        intro n m l φ ψ
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        exact congrArg (fun f ↦ f.left) (V.map_comp φ ψ) }
  have heq : Vq ⋙ G = V := by rfl
  have hz : Presieve.singleton (V _⦋0⦌).hom ∈ precoverage X U := by
    let c : Cone (V.properFaceDiagram 0) :=
      ⟨Over.mk (𝟙 U),
        { app := fun a ↦ (Nat.not_lt_zero _ a.unop.property.1).elim
          naturality := fun a b f ↦ (Nat.not_lt_zero _ a.unop.property.1).elim }⟩
    have hc : IsLimit c :=
      { lift := fun s ↦ Over.mkIdTerminal.from s.pt
        fac := fun s j ↦ (Nat.not_lt_zero _ j.unop.property.1).elim
        uniq := fun s m hm ↦ Over.mkIdTerminal.hom_ext _ _ }
    let κ : V _⦋0⦌ ⟶ c.pt := Over.mkIdTerminal.from _
    have hκ : ∀ a : SimplicialObject.ProperFaceCategory 0,
        κ ≫ c.π.app (op a) = V.map a.obj.hom.op :=
      fun a ↦ (Nat.not_lt_zero _ a.property.1).elim
    let := hFepi 0
    let := matching_epi_of_properFace K F V (Over.post Y) eb 0
      (M 0) (hlim 0).some (μ 0) (hproj 0) c hc κ hκ
    have h := Over.epi_left_of_epi ((Over.post Y).map κ)
    have h' : Epi (Y.map κ.left) := h
    rw [show κ.left = (V _⦋0⦌).hom from Over.mkIdTerminal_from_left _] at h'
    let := hVqc 0
    let := T.property.2
    exact singleton_cover_of_representable_epi X _
      (yoneda_epi_of_ulift (topology X) _ h')
  apply hypercover_spectrum_replacement X U V hterms hz
  intro n
  let := properFace_finCategory (n + 1)
  let d := Vq.properFaceDiagram (n + 1)
  let cQ := limit.cone d
  let kQ : Cone d :=
    ⟨Vq _⦋n + 1⦌,
      { app := fun a ↦ Vq.map a.unop.obj.hom.op
        naturality := by
          intro a b φ
          dsimp [d, SimplicialObject.properFaceDiagram]
          rw [Category.id_comp, ← Vq.map_comp, ← op_comp, Over.w] }⟩
  let κQ : Vq _⦋n + 1⦌ ⟶ cQ.pt := limit.lift d kQ
  let c : Cone (V.properFaceDiagram (n + 1)) := G.mapCone cQ
  have hc : IsLimit c := isLimitOfPreserves G (limit.isLimit d)
  let κ : V _⦋n + 1⦌ ⟶ c.pt := G.map κQ
  have hκ : ∀ a : SimplicialObject.ProperFaceCategory (n + 1),
      κ ≫ c.π.app (op a) = V.map a.obj.hom.op := by
    intro a
    change G.map κQ ≫ G.map (cQ.π.app (op a)) = _
    rw [← G.map_comp]
    exact congrArg G.map (limit.lift_π kQ (op a))
  let := hFepi (n + 1)
  let := matching_epi_of_properFace K F V (Over.post Y) eb (n + 1)
    (M (n + 1)) (hlim (n + 1)).some (μ (n + 1)) (hproj (n + 1)) c hc κ hκ
  have hep := Over.epi_left_of_epi ((Over.post Y).map κ)
  have hep' := yoneda_epi_of_ulift (topology X) κ.left hep
  let := hVqc (n + 1)
  have : QuasiSeparatedSpace c.pt.left.left := cQ.pt.left.property.2
  exact ⟨c, κ, ⟨hc⟩, singleton_cover_of_representable_epi X κ.left hep', hκ⟩
