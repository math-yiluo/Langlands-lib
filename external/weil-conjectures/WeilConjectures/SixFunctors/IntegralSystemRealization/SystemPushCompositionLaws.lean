/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.SystemPushIdentityPullUnit
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence

/-! # Identity normalization of the system direct-image compositor

Source: Stacks 07A7, 0F7C; blueprint fix-prop-coherence, composition clause.
(blueprint: lem-sf-system-push-identity-pair).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The two-identity proper-image compositor is the image of the canonical identity
comparison. This concerns direct image only, before compactification or interchange.
Source: Stacks 07A7, 0F7C; blueprint fix-prop-coherence, composition clause
(blueprint: lem-sf-system-push-identity-pair).

Proof: the sections normalization identifies the ordinary two-identity compositor
with direct image of the ordinary identity comparison. The latter comparison is
fixed by the sectionwise identity presentation of CanonicalBridge. Conjugate the
ordinary equality under the inverse-image adjunctions, then localize whole
complexes. The field Compositors.pullComp_model identifies the resulting derived
inverse-image comparison with the recorded pullback compositor. Conjugating under
the chosen derived adjunctions gives its direct-image mate Compositors.pushComp.
The mate of the ordinary identity comparison is exactly CanonicalBridge.push
followed by the intrinsic semilinear sId. Naturality of this identity isomorphism
identifies its component at S_id M with S_id of its component at M, yielding the
displayed equality. Equality transports for id composed with id are inserted at
the output. No finite evaluation or faithfulness of evaluations is used.
-/
private theorem conjugateTransport
    {A B I : Type*} [Category A] [Category B]
    (L : I → A ⥤ B) (R₀ : I → B ⥤ A) (a : ∀ i, L i ⊣ R₀ i)
    {L' : A ⥤ B} {R' : B ⥤ A} (a' : L' ⊣ R')
    {i j : I} (e : i = j) (d : L i ≅ L') :
    conjugateIsoEquiv a' (a j) (eqToIso (congrArg L e.symm) ≪≫ d) =
      conjugateIsoEquiv a' (a i) d ≪≫ eqToIso (congrArg R₀ e) := by
  cases e
  simp

theorem systemPushIdentityPair (o : Operations l E) (c : Compositors l E o)
    (b : CanonicalBridge l E o) (X : Scheme.{u}) (M : System l E X) :
      (c.pushComp l E (𝟙 X) (𝟙 X)).hom.app M ≫
          eqToHom (congrArg (fun k ↦ (Operations.push l E o k).obj M)
            (Category.id_comp (𝟙 X))) =
        (Operations.push l E o (𝟙 X)).map
          ((b.push l E (𝟙 X) ≪≫
            ProEtale.SemilinearProperOpen.sId (scalarRings l E)
              (scalarTransitions l E) X).hom.app M) := by
  obtain ⟨e, he, hb⟩ := systemPushIdentityPullUnit l E o c b X
  let k := eqToIso (congrArg (pull l E) (Category.id_comp (𝟙 X)).symm) ≪≫
    c.pullComp (𝟙 X) (𝟙 X)
  have hk : conjugateIsoEquiv ((o.direct (𝟙 X)).adj.comp (o.direct (𝟙 X)).adj)
      (o.direct (𝟙 X)).adj k =
      Functor.isoWhiskerRight
        (conjugateIsoEquiv (o.direct (𝟙 X)).adj Adjunction.id e.symm)
        (Operations.push l E o (𝟙 X)) ≪≫
        Functor.leftUnitor (Operations.push l E o (𝟙 X)) := by
    apply ProEtale.StrictTower.conjugate_unit
      (o.direct (𝟙 X)).adj (o.direct (𝟙 X)).adj e k
    simpa only [k, Iso.trans_assoc] using he
  have ht : c.pushComp l E (𝟙 X) (𝟙 X) ≪≫
      eqToIso (congrArg (Operations.push l E o)
        (Category.id_comp (𝟙 X))) =
      conjugateIsoEquiv ((o.direct (𝟙 X)).adj.comp (o.direct (𝟙 X)).adj)
        (o.direct (𝟙 X)).adj k := by
    unfold Compositors.pushComp k
    have htr := conjugateTransport
      (fun f : X ⟶ X ↦ pull l E f)
      (fun f : X ⟶ X ↦ Operations.push l E o f)
      (fun f ↦ (o.direct f).adj)
      ((o.direct (𝟙 X)).adj.comp (o.direct (𝟙 X)).adj)
      (Category.id_comp (𝟙 X)) (c.pullComp (𝟙 X) (𝟙 X))
    simpa only [k, Compositors.pushComp] using htr.symm
  rw [← hb]
  have hiso := ht.trans hk
  have hm := congrArg Iso.hom hiso
  have hcomp := congr_app hm M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hcomp
  simpa using hcomp

end WeilConjectures.IntegralSystemRealization
