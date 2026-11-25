/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafTransport
import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction

/-!
# Localization in the native Weil sheaf heart

Source: Stacks Project, Tags 09AH and 09BM; native coefficient and Frobenius constructions
in WeilConjectures/SixFunctors/ProEtale/Adic and WeilConjectures/WeilSheaf.
(blueprint: lem-sf-native-weil-immersion-heart-localization)

The three statements give the coefficient comparisons, exact constructible operations,
and the natural short exact sequence of the actual lifted adjunction maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

namespace AlgebraicGeometry

open ProEtale
open scoped ProEtale CategoryTheory.Obj

-- Match the coefficient instances of the public imports. The proof-only imports also
-- expose a commutative-ring shortcut, whose use forces expensive sheaf-functor conversions.
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing
  ULift.commRing AlgebraicClosure.instCommRing

private noncomputable def nativeOpenAdjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j := by
  apply Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

private lemma shortExact_of_jointly_detected
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (P : C ⥤ D) (Q : C ⥤ E) [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (detect : ∀ M, IsZero (P.obj M) → IsZero (Q.obj M) → IsZero M)
    (S : ShortComplex C) (hP : (S.map P).ShortExact)
    (hQ : (S.map Q).ShortExact) : S.ShortExact := by
  have hkerP : IsZero (P.obj (kernel S.f)) := by
    have hm : Mono (P.map S.f) := hP.mono_f
    exact (isZero_kernel_of_mono (P.map S.f)).of_iso (PreservesKernel.iso P S.f)
  have hkerQ : IsZero (Q.obj (kernel S.f)) := by
    have hm : Mono (Q.map S.f) := hQ.mono_f
    exact (isZero_kernel_of_mono (Q.map S.f)).of_iso (PreservesKernel.iso Q S.f)
  have hcokerP : IsZero (P.obj (cokernel S.g)) := by
    have he : Epi (P.map S.g) := hP.epi_g
    exact (isZero_cokernel_of_epi (P.map S.g)).of_iso (PreservesCokernel.iso P S.g)
  have hcokerQ : IsZero (Q.obj (cokernel S.g)) := by
    have he : Epi (Q.map S.g) := hQ.epi_g
    exact (isZero_cokernel_of_epi (Q.map S.g)).of_iso (PreservesCokernel.iso Q S.g)
  have hhomP : IsZero (P.obj S.homology) :=
    ((S.map P).exact_iff_isZero_homology.1 hP.exact).of_iso (S.mapHomologyIso P).symm
  have hhomQ : IsZero (Q.obj S.homology) :=
    ((S.map Q).exact_iff_isZero_homology.1 hQ.exact).of_iso (S.mapHomologyIso Q).symm
  have : Mono S.f := Preadditive.mono_of_isZero_kernel _ (detect _ hkerP hkerQ)
  have : Epi S.g := Preadditive.epi_of_isZero_cokernel _ (detect _ hcokerP hcokerQ)
  exact ⟨S.exact_iff_isZero_homology.2 (detect _ hhomP hhomQ)⟩

private lemma shortExact_of_localization
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (P : C ⥤ D) (Q : C ⥤ E) (J : D ⥤ C) (I : E ⥤ C)
    [P.Additive] [Q.Additive] [J.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (aj : J ⊣ P) (ai : Q ⊣ I)
    (hj : ∀ N, IsIso (aj.unit.app N)) (hi : ∀ N, IsIso (ai.counit.app N))
    (hPI : ∀ N, IsZero (P.obj (I.obj N)))
    (hQJ : ∀ N, IsZero (Q.obj (J.obj N)))
    (detect : ∀ M, IsZero (Q.obj M) → IsZero (P.obj M) → IsZero M) (M : C) :
    ∃ h : aj.counit.app M ≫ ai.unit.app M = 0,
      (ShortComplex.mk (aj.counit.app M) (ai.unit.app M) h).ShortExact := by
  have h : aj.counit.app M ≫ ai.unit.app M = 0 := by
    have hn := aj.counit.naturality (ai.unit.app M)
    have hz : P.map (ai.unit.app M) = 0 := (hPI _).eq_of_tgt _ _
    change J.map (P.map (ai.unit.app M)) ≫ aj.counit.app _ =
      aj.counit.app M ≫ ai.unit.app M at hn
    rw [hz, Functor.map_zero, zero_comp] at hn
    exact hn.symm
  refine ⟨h, ?_⟩
  let S := ShortComplex.mk (aj.counit.app M) (ai.unit.app M) h
  apply shortExact_of_jointly_detected Q P detect S
  · have hc : IsIso (ai.counit.app (Q.obj M)) := hi _
    have hg : IsIso (Q.map (ai.unit.app M)) := by
      rw [← IsIso.inv_eq_of_inv_hom_id (ai.left_triangle_components M)]
      infer_instance
    have hf : (S.map Q).f = 0 := (hQJ _).eq_of_src _ _
    have : Mono (S.map Q).f := ⟨fun a b _ ↦ (hQJ _).eq_of_tgt a b⟩
    have : Epi (S.map Q).g := inferInstanceAs (Epi (Q.map (ai.unit.app M)))
    exact ⟨(ShortComplex.exact_iff_mono _ hf).2
      (inferInstanceAs (Mono (Q.map (ai.unit.app M))))⟩
  · have hu : IsIso (aj.unit.app (P.obj M)) := hj _
    have hf : IsIso (P.map (aj.counit.app M)) := by
      rw [← IsIso.inv_eq_of_hom_inv_id (aj.right_triangle_components M)]
      infer_instance
    have hg : (S.map P).g = 0 := (hPI _).eq_of_tgt _ _
    have : Epi (S.map P).g := ⟨fun a b _ ↦ (hPI _).eq_of_src a b⟩
    have : Mono (S.map P).f := inferInstanceAs (Mono (P.map (aj.counit.app M)))
    exact ⟨(ShortComplex.exact_iff_epi _ hg).2
      (inferInstanceAs (Epi (P.map (aj.counit.app M))))⟩

private lemma coefficient_square (l : ℕ) [Fact l.Prime]
    {Y A B T : Scheme.{u}} (a : Y ⟶ A) (b : A ⟶ T) (c : Y ⟶ B) (d : B ⟶ T)
    (h : a ≫ b = c ≫ d) :
    (a)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l b) ≫
        upperStarAdicConstantSheafHom l a =
      (upperStarCompIso (WeilCoefficients.{u} l) h).hom.app (adicConstantSheaf l T) ≫
        (c)^*[WeilCoefficients.{u} l].map (upperStarAdicConstantSheafHom l d) ≫
          upperStarAdicConstantSheafHom l c := by
  rw [← cancel_epi ((upperStarComp (WeilCoefficients.{u} l) a b).hom.app
    (adicConstantSheaf l T))]
  simp only [upperStarCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [upperStarAdicConstantSheafHom_comp, upperStarAdicConstantSheafHom_comp]
  have hc : ∀ (f g : Y ⟶ T) (h : f = g),
      (upperStarCongr (WeilCoefficients.{u} l) h).hom.app (adicConstantSheaf l T) ≫
        upperStarAdicConstantSheafHom l g = upperStarAdicConstantSheafHom l f := by
    intro f g h
    subst g
    simp [upperStarCongr]
  exact (hc _ _ h).symm

attribute [local irreducible] Scheme.Hom.geometricFiber
  Scheme.Hom.geometricFiberMap Scheme.Hom.geometricGaloisFrobenius

attribute [local semireducible] Scheme.Hom.geometricFiber
  Scheme.Hom.geometricFiberMap Scheme.Hom.geometricGaloisFrobenius

/-- The actual open and closed adjunction maps form a natural short exact sequence
in the category of all native pro-etale Weil sheaves.

Source: Stacks Project, Tags 09AH and 09BM; the native coefficient, module and
fixed-pair constructions cited in this node.
(blueprint: lem-sf-native-weil-immersion-heart-localization)

Proof plan:
1. Base change preserves the two immersion conditions by
   [lem-weil-pbc-open-immersion-base-change] and [lem-weil-pbc-closed-immersion-base-change],
   and preserves quasi-compactness of j by [lem-weil-pbc-qcqs-morphism-permanence](3). Their
   images are complementary after base change: on an affine chart the closed part is defined by
   the extended ideal, and the complementary basic opens are its complement. Choose a finite
   affine cover of X by spectra of finitely generated k_0-algebras. Its base changes are spectra
   of finitely generated k-algebras, hence Noetherian by [lem-wf-affine-noetherian-components].
   A descending chain of closed subsets of the union stabilizes as soon as its restrictions to
   all finitely many charts do. Thus \bar X is Noetherian and quasi-compact. The same holds for
   its open subscheme \bar U and its closed subscheme \bar Z: affine charts on the latter are
   quotient rings. These schemes are locally of finite type over k, and U,Z are locally of
   finite type over k_0. Quasi-separatedness follows since intersections of affine opens in a
   Noetherian space are quasi-compact. In particular the qcqs hypotheses of the ringed
   localization and finite-stratification lemmas hold. None of this requires separatedness or a
   radical defining ideal.
Uses: lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-qcqs-morphism-permanence, lem-wf-affine-noetherian-components.
2. Apply [lem-sf-native-adic-pullback-exact-lisse] to \bar j and \bar i. It identifies the
   canonical maps \bar j^{-1}B_X\to B_U and \bar i^{-1}B_X\to B_Z as isomorphisms and identifies
   their module pullbacks with exact inverse images. These are isomorphisms of rings: each
   coefficient map is precomposition, so preserves addition, multiplication and 1. For any
   composable maps a,b and a local function t, (t\circ a)\circ b=t\circ(a\circ b). Apply this
   equality to \bar hF_V=F_W\bar h, for h=i,j, to obtain precisely compatibility with the
   framework's Frobenius coefficient comparisons. The composition and identity comparisons in
   the cited lemma show that F_W^* and (F_W^{-1})^* are inverse additive functors. More
   concretely, [lem-weil-proetale-isomorphism-inverse-image] describes this as reindexing site
   objects by F_W and its inverse; the coefficient action is carried along the same
   precomposition isomorphism.
Uses: lem-sf-native-adic-pullback-exact-lisse, lem-weil-proetale-isomorphism-inverse-image,
   def-sf-native-weil-derived-framework.
3. For W=X,U,Z, [lem-sf-native-weil-constructible-abelian] gives the abelian category \mathcal
   W_W and an exact conservative forgetful functor For_W to \mathcal A_W. It also reflects
   exactness. Indeed, for a composable pair with zero composite, exactness of For identifies the
   underlying kernel, image and the quotient of the kernel by the image with those of the
   underlying sequence. If that sequence is exact, this quotient maps to zero; conservativity
   applied to its map to zero makes the quotient itself zero. The same argument for the first
   kernel and last cokernel detects injectivity and surjectivity. Thus a sequence in the
   fixed-pair category is short exact exactly when its carrier sequence is short exact. This
   argument is in the abelian category of all fixed pairs and imposes no constructibility
   hypothesis on the sequence.
Uses: lem-sf-native-weil-constructible-abelian.
4. Use B=B_X and the coefficient identifications of step 2 in
   [proposition-extension-zero-restriction-closed-subscheme]. Its operations are the actual
   ring-module operations, so it gives the exact underlying open extension J_0, its adjunction
   J_0\dashv P_0, exact closed direct image I_0, invertible closed counit Q_0I_0\to\mathrm{id},
   P_0I_0=0, and the short exact sequence of the actual open counit and closed unit. The other
   adjunction Q_0\dashv I_0 is the canonical tensor-pullback/module-pushforward adjunction of
   [lem-weil-pbc-ringed-topoi-module-adjunction]; its coefficient map is precomposition, as in
   the framework. Both P_0,Q_0 are additive exact functors by
   [lem-sf-native-adic-pullback-exact-lisse]. Direct image is additive because addition is taken
   on sections. Extension by zero is additive since its presheaf construction and sheafification
   carry sums of maps to sums. These descriptions agree with the module actions after the
   specified coefficient isomorphisms, rather than changing the coefficient category.
   Explicitly, for c:\bar i^{-1}B_X\xrightarrow{\sim}B_Z the map \bar i^{-1}M\to
   B_Z\otimes_{\bar i^{-1}B_X}\bar i^{-1}M, m\mapsto1\otimes m, is an isomorphism of sheaves
   (scalars transported along c), and under it the Hom bijection of the ringed-topoi adjunction
   sends a map to its composite with the sheaf unit M\to\bar i_*\bar i^{-1}M, exactly as for the
   module-object adjunction of the cited localization node. Hence Q_0\dashv I_0 has the same
   unit M\to I_0Q_0M as in its (3); the same holds for P_0 with j.
Uses: proposition-extension-zero-restriction-closed-subscheme,
lem-weil-pbc-ringed-topoi-module-adjunction,
   lem-sf-native-adic-pullback-exact-lisse, def-sf-native-weil-derived-framework.
5. Normalize the Frobenius comparisons using actual reindexing. Write T_W=F_W^*. By
   [lem-weil-proetale-isomorphism-inverse-image] and step 2, T_W is the ringed reindexing
   equivalence. Pullback composition gives T_UP_0\cong P_0T_X and T_ZQ_0\cong Q_0T_X. Reindexing
   direct image identifies the values at V via the canonical equality of the two fibre products
   V\times_{\bar X}\bar Z obtained from F_X\bar i=\bar iF_Z. This is the framework's comparison
   T_XI_0\cong I_0T_Z. It is the normalized right-adjoint comparison: the sheaf Hom transpose
   sends a map Q_0M\to N to its adjunct M\to I_0N, and reindexing sends both maps to their
   restrictions along those same object isomorphisms. The tensor factor is changed by the
   precomposition ring map of step 2, so this equality also holds for module maps. Apply
   [lem-sfb-equivalence-square-inverse-mate-coherence](1), with the Frobenius equivalences and
   the same adjunction on each side: this equality of Hom bijections identifies the displayed
   direct comparison with the mate of the inverse pullback comparison.  For J_0\dashv P_0 the
   same check applies to the framework's natural extension-by-zero comparison. Since F_X\bar
   j=\bar jF_U, the site isomorphism of [lem-weil-proetale-isomorphism-inverse-image](1) for F_X
   restricts to that for F_U on objects over \bar U, so T_X carries the extension-by-zero
   presheaf P_M at \bar U to the one of T_UM, and commutes with sheafification (an equivalence);
   this is the comparison T_XJ_0\cong J_0T_U. A map J_0M\to N and its adjunct M\to P_0N agree
   over \bar U, and reindexing restricts both along the same object isomorphisms, so T commutes
   with the Hom bijections of J_0\dashv P_0. By the uniqueness in
   [lem-sfb-equivalence-square-inverse-mate-coherence](1) (E_A=T_U, E_B=T_X, u the pullback
   comparison) the extension-by-zero comparison is the normalized one: its inverse has mate the
   pullback comparison. Both framework comparisons thus satisfy the mate hypothesis, with the
   actual units and counits.
Uses: lem-weil-proetale-isomorphism-inverse-image,
   lem-sfb-equivalence-square-inverse-mate-coherence, def-sf-native-weil-derived-framework,
   lem-weil-pbc-ringed-topoi-module-adjunction.
6. Apply [lem-sf-fixed-pair-adjunction-lift] to J_0\dashv P_0 and Q_0\dashv I_0 with the
   comparisons of step 5. Its lifted functors send (M,\phi) to (GM,G(\phi)\circ c_M), exactly
   the definition of the four functors in [def-sf-native-weil-derived-framework]. Hence it
   supplies J\dashv P and Q\dashv I, with the underlying ordinary sheaf units and counits. In
   particular the two maps \varepsilon_M:JPM\to M and \eta_M:M\to IQM are morphisms in \mathcal
   W_X. If \theta denotes the structure on M and \theta_{JP},\theta_{IQ} those on the outer
   terms, their commuting equations are \varepsilon_M\circ\theta_{JP}=\theta\circ
   T_X(\varepsilon_M),\qquad \eta_M\circ\theta=\theta_{IQ}\circ T_X(\eta_M). These are the
   fixed-pair morphism equations furnished by the lemma, not an additional choice of Frobenius
   structure on either outer term. Naturality and both triangle identities are retained by the
   lifted adjunction.
Uses: lem-sf-fixed-pair-adjunction-lift, def-sf-native-weil-derived-framework.
10. For M\in\mathcal W_X, the two actual maps of step 6 have, after forgetting, precisely the
   counit and unit sequence of [proposition-extension-zero-restriction-closed-subscheme](3) for its
   carrier. That sequence is short exact. Their composite is zero because the carrier composite is
   zero and forgetting fixed pairs is faithful (its morphisms are commuting carrier maps by
   [def-sf-native-weil-derived-framework]). By the reflection argument of step 3 it is a short
   exact sequence in \mathcal W_X. Naturality follows from the naturality of the two lifted
   adjunction maps. The proof did not impose constructibility on M.  If U is empty, extension by
   zero from its zero module category is zero and the sequence reads 0\to0\to
   M\xrightarrow{\sim}IQM\to0. If Z is empty it reads 0\to JPM\xrightarrow{\sim}M\to0\to0. The
   cited ringed localization theorem applies to either case; the isomorphisms also follow from
   exactness of these displayed sequences. In the constructibility argument, omit empty strata
   and use rank zero on the complement. Every closed-immersion input above permits arbitrary
   ideal sheaves, so nilpotents in Z have not been removed or excluded.
Uses: proposition-extension-zero-restriction-closed-subscheme,
lem-sf-native-weil-constructible-abelian,
   def-sf-native-weil-derived-framework.
-/
theorem ProEtaleWeilSheaf.nativeImmersionHeartLocalization
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    (X U Z : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    ∃ (aj : ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣
        ProEtaleWeilSheaf.upperStar k₀ l j)
      (ai : ProEtaleWeilSheaf.upperStar k₀ l i ⊣ ProEtaleWeilSheaf.lowerStar k₀ l i),
      (∀ N : ProEtaleWeilSheaf k₀ l U,
        (aj.unit.app N).hom.f =
          (adicOpenImmersionLowerShriekAdjunction l
            (Scheme.Hom.geometricFiberMap j
              (comp_over j (Spec (CommRingCat.of k₀))))).unit.app N.carrier) ∧
      (∀ M : ProEtaleWeilSheaf k₀ l X,
        (aj.counit.app M).hom.f =
          (adicOpenImmersionLowerShriekAdjunction l
            (Scheme.Hom.geometricFiberMap j
              (comp_over j (Spec (CommRingCat.of k₀))))).counit.app M.carrier) ∧
      (∀ M : ProEtaleWeilSheaf k₀ l X,
        (ai.unit.app M).hom.f =
          (adicUpperStarLowerStarAdjunction l
            (Scheme.Hom.geometricFiberMap i
              (comp_over i (Spec (CommRingCat.of k₀))))).unit.app M.carrier) ∧
      (∀ N : ProEtaleWeilSheaf k₀ l Z,
        (ai.counit.app N).hom.f =
          (adicUpperStarLowerStarAdjunction l
            (Scheme.Hom.geometricFiberMap i
              (comp_over i (Spec (CommRingCat.of k₀))))).counit.app N.carrier) ∧
      ∀ M : ProEtaleWeilSheaf k₀ l X,
        ∃ h : aj.counit.app M ≫ ai.unit.app M = 0,
          (ShortComplex.mk (aj.counit.app M) (ai.unit.app M) h).ShortExact := by
  let aj := nativeOpenAdjunction k₀ l j
  let ai := ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i
  refine ⟨aj, ai, (fun _ ↦ rfl), (fun _ ↦ rfl), (fun _ ↦ rfl), (fun _ ↦ rfl), ?_⟩
  intro M
  apply shortExact_of_localization
    (ProEtaleWeilSheaf.upperStar k₀ l j) (ProEtaleWeilSheaf.upperStar k₀ l i)
    (ProEtaleWeilSheaf.extensionByZero k₀ l j) (ProEtaleWeilSheaf.lowerStar k₀ l i)
    aj ai
  · intro N
    have : IsIso ((IsoAlgebra.forget _).map (aj.unit.app N)) :=
      inferInstanceAs (IsIso ((adicOpenImmersionLowerShriekAdjunction l
        (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app N.carrier))
    exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)
  · intro N
    exact inferInstanceAs (IsIso
      ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l i).counit.app N))
  · exact ProEtaleWeilSheaf.isZero_upperStar_obj_lowerStar_obj i j hij
  · intro N
    apply (ProEtaleWeilSheaf.isZero_iff _).2
    exact isZero_adicUpperStar_adicOpenImmersionLowerShriek _ _
      (Set.disjoint_iff_inter_eq_empty.1
        (Scheme.Hom.isCompl_range_geometricFiberMap i j _ _ hij).disjoint.symm) _
  · exact ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij

end AlgebraicGeometry
