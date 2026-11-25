/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerAdjunction
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Finiteness.Ideal

/-! # The ramified finite quotient square on coefficient sections

Source: the quotient-ideal calculation in Step 1 of
`lem-pur-finite-quotient-module-balancing`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar

private instance constantRingWeakSheafify (W : Scheme.{u}) :
    (sheafToPresheaf (ProEt.topology W) CommRingCat.{u + 1}).IsRightAdjoint :=
  (integralCoefficientRingSheafify.{u, u} W).isRightAdjoint

private noncomputable instance constantTypeSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) (Type (u + 1)) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  exact hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _

private instance constantTypeWeakSheafify (W : Scheme.{u}) :
    (sheafToPresheaf (ProEt.topology W) (Type (u + 1))).IsRightAdjoint :=
  (constantTypeSheafify W).isRightAdjoint

private instance constantRingLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective CommRingCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1, u + 1, u + 1} _

-- All these arguments take place on the actual site; evaluation of arbitrary
-- sheaf colimits is never used.
private theorem constant_surjective (W : Scheme.{u}) {A B : CommRingCat.{u + 1}}
    (f : A ⟶ B) (hf : Function.Surjective f) (U : W.ProEtᵒᵖ) :
    Function.Surjective
      (((constantSheaf (ProEt.topology W) CommRingCat).map f).hom.app U) := by
  classical
  let J := ProEt.topology W
  let e := constantCommuteCompose J (forget CommRingCat.{u + 1})
  let s := (constantSheaf J (Type (u + 1))).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s ≫ (constantSheaf J (Type (u + 1))).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type (u + 1))).map (𝟙 ((forget CommRingCat).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type (u + 1))).map_id _
  let r := e.hom.app B ≫ s ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat)).map
      ((constantSheaf J CommRingCat).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat ⋙ sheafCompose J (forget CommRingCat)).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s ≫
      (constantSheaf J (Type (u + 1))).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s, hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  exact ⟨r.hom.app U x, congrArg (fun h ↦ h.hom.app U x) hr⟩

private noncomputable def constantFunction (W : Scheme.{u})
    (A : CommRingCat.{u + 1}) (f : A → A) :
    ((constantSheaf (ProEt.topology W) CommRingCat).obj A).obj ⋙ forget CommRingCat ⟶
      ((constantSheaf (ProEt.topology W) CommRingCat).obj A).obj ⋙ forget CommRingCat :=
  let J := ProEt.topology W
  let P := (Functor.const W.ProEtᵒᵖ).obj A
  let e := sheafifyComposeIso J (forget CommRingCat) P
  e.inv ≫ sheafifyMap J ((Functor.const W.ProEtᵒᵖ).map (TypeCat.ofHom f)) ≫ e.hom

private theorem constantFunction_constant (W : Scheme.{u}) (A : CommRingCat.{u + 1})
    (f : A → A) (U : W.ProEtᵒᵖ) (a : A) :
    (constantFunction W A f).app U
        ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app U a) =
      (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app U (f a) := by
  let J := ProEt.topology W
  let P := (Functor.const W.ProEtᵒᵖ).obj A
  have h : Functor.whiskerRight (toSheafify J P) (forget CommRingCat) ≫
      constantFunction W A f =
      (Functor.const W.ProEtᵒᵖ).map (TypeCat.ofHom f) ≫
        Functor.whiskerRight (toSheafify J P) (forget CommRingCat) := by
    dsimp only [constantFunction]
    rw [← Category.assoc, ← Category.assoc, sheafComposeIso_inv_fac,
      ← toSheafify_naturality, Category.assoc]
    erw [sheafComposeIso_hom_fac]
  exact congrArg (fun t ↦ t.app U a) h

private theorem constant_kernel (W : Scheme.{u}) {A B : CommRingCat.{u + 1}}
    (f : A ⟶ B) (hfg : (RingHom.ker f.hom).FG) (U : W.ProEtᵒᵖ) :
    RingHom.ker (((constantSheaf (ProEt.topology W) CommRingCat).map f).hom.app U).hom =
      (RingHom.ker f.hom).map
        ((toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj A)).app U).hom := by
  classical
  let J := ProEt.topology W
  let K := RingHom.ker f.hom
  let P := (Functor.const W.ProEtᵒᵖ).obj A
  let R := ((constantSheaf J CommRingCat).obj A).obj
  let η : P ⟶ R := toSheafify J P
  let Q := (Functor.const W.ProEtᵒᵖ).obj B
  let ε := toSheafify J Q
  let q := ((constantSheaf J CommRingCat).map f).hom
  have hR : Presheaf.IsSheaf J R := ((constantSheaf J CommRingCat).obj A).property
  have hη (V V' : W.ProEtᵒᵖ) (k : V ⟶ V') (a : A) :
      R.map k (η.app V a) = η.app V' a :=
    (NatTrans.naturality_apply η k a).symm
  have hq (V : W.ProEtᵒᵖ) (a : A) :
      q.app V (η.app V a) = ε.app V (f a) := by
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality J
      ((Functor.const W.ProEtᵒᵖ).map f)) V) a).symm
  obtain ⟨d, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    hfg
  have hg' : Ideal.span (Set.range g) = K := by
    simpa only [Ideal.submodule_span_eq] using hg
  have hex (a : A) (ha : a ∈ K) : ∃ c : Fin d → A, ∑ i, c i * g i = a :=
    Ideal.mem_span_range_iff_exists_fun.mp (hg'.symm ▸ ha)
  let c : A → Fin d → A := fun a ↦ if ha : a ∈ K then (hex a ha).choose else 0
  have hc (a : A) (ha : a ∈ K) : ∑ i, c a i * g i = a := by
    simpa only [c, dite_eq_left ha] using (hex a ha).choose_spec
  let t (i : Fin d) := constantFunction W A (fun a ↦ c a i)
  have htn (i : Fin d) {V V' : W.ProEtᵒᵖ} (k : V ⟶ V') (y : R.obj V) :
      R.map k ((t i).app V y) = (t i).app V' (R.map k y) :=
    (NatTrans.naturality_apply (t i) k y).symm
  apply le_antisymm
  · intro x hx
    have hxq : q.app U x = 0 := hx
    have heq : (∑ i, (show R.obj U from (t i).app U x) * η.app U (g i)) = x := by
      apply hR.isSeparated _ _ (Presheaf.imageSieve_mem J η x)
      intro V k hk
      obtain ⟨a, ha⟩ := hk
      change A at a
      have hqa : ε.app (op V) (f a) = ε.app (op V) 0 := by
        rw [← hq, ha, NatTrans.naturality_apply q, hxq, map_zero, map_zero]
      apply hR.isSeparated _ _ (Presheaf.equalizerSieve_mem J ε _ _ hqa)
      intro V' k' hk'
      have hak : a ∈ K := (show f a = 0 from hk')
      have hax : R.map k'.op (R.map k.op x) = η.app (op V') a := by
        rw [← ha, hη]
      have ht (i : Fin d) :
          R.map k'.op (R.map k.op ((t i).app U x)) = η.app (op V') (c a i) := by
        rw [htn, htn, hax]
        exact constantFunction_constant W A _ _ _
      simp only [map_sum, map_mul, ht, hη]
      simp_rw [← map_mul]
      rw [← map_sum]
      exact congrArg (η.app (op V')) (hc a hak) |>.trans hax.symm
    rw [← heq]
    apply Submodule.sum_mem
    intro j _
    apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem
    change g j ∈ K
    rw [← hg']
    exact Ideal.subset_span (Set.mem_range_self j)
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change q.app U (η.app U a) = 0
    rw [hq, show f a = 0 from ha, map_zero]

private theorem pushout_of_kernels {A B C D : CommRingCat.{u + 1}}
    (f : A ⟶ B) (q : A ⟶ C) (r : B ⟶ D) (s : C ⟶ D)
    (hw : f ≫ r = q ≫ s) (hq : Function.Surjective q) (hr : Function.Surjective r)
    (hk : (RingHom.ker q.hom).map f.hom = RingHom.ker r.hom) :
    IsPushout f q r s := by
  classical
  apply IsPushout.of_isColimit (c := PushoutCocone.mk r s hw)
  apply PushoutCocone.isColimitAux'
  intro t
  have hker : RingHom.ker r.hom ≤ RingHom.ker t.inl.hom := by
    rw [← hk, Ideal.map_le_iff_le_comap]
    intro a ha
    have ht := ConcreteCategory.congr_hom t.condition a
    change t.inl (f a) = t.inr (q a) at ht
    change t.inl (f a) = 0
    rw [show q a = 0 from ha, map_zero] at ht
    exact ht
  let δ : D ⟶ t.pt := CommRingCat.ofHom
    (r.hom.liftOfSurjective hr ⟨t.inl.hom, hker⟩)
  have hd (b : B) : δ (r b) = t.inl b :=
    RingHom.liftOfSurjective_comp_apply _ _ _ _
  refine ⟨δ, ?_, ?_, ?_⟩
  · ext b
    exact hd b
  · ext c
    obtain ⟨a, rfl⟩ := hq c
    have hw' := ConcreteCategory.congr_hom hw a
    change r (f a) = s (q a) at hw'
    change δ (s (q a)) = t.inr (q a)
    rw [← hw', hd]
    exact ConcreteCategory.congr_hom t.condition a
  · intro m hm _
    ext d
    obtain ⟨b, rfl⟩ := hr d
    exact (ConcreteCategory.congr_hom hm b).trans (hd b).symm

private theorem constant_pushout (W : Scheme.{u})
    {A B C D : CommRingCat.{u + 1}}
    (f : A ⟶ B) (q : A ⟶ C) (r : B ⟶ D) (s : C ⟶ D)
    (hw : f ≫ r = q ≫ s) (hq : Function.Surjective q) (hr : Function.Surjective r)
    (hk : (RingHom.ker q.hom).map f.hom = RingHom.ker r.hom)
    (hqfg : (RingHom.ker q.hom).FG) (hrfg : (RingHom.ker r.hom).FG)
    (U : W.ProEtᵒᵖ) :
    IsPushout (((constantSheaf (ProEt.topology W) CommRingCat).map f).hom.app U)
      (((constantSheaf (ProEt.topology W) CommRingCat).map q).hom.app U)
      (((constantSheaf (ProEt.topology W) CommRingCat).map r).hom.app U)
      (((constantSheaf (ProEt.topology W) CommRingCat).map s).hom.app U) := by
  let J := ProEt.topology W
  let ηA := (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj A)).app U
  let ηB := (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj B)).app U
  let fU := ((constantSheaf J CommRingCat).map f).hom.app U
  have hw' : (constantSheaf J CommRingCat).map f ≫
        (constantSheaf J CommRingCat).map r =
      (constantSheaf J CommRingCat).map q ≫ (constantSheaf J CommRingCat).map s := by
    rw [← Functor.map_comp, ← Functor.map_comp, hw]
  apply pushout_of_kernels
  · exact congrArg (fun k ↦ k.hom.app U) hw'
  · exact constant_surjective W q hq U
  · exact constant_surjective W r hr U
  · rw [constant_kernel W q hqfg U, constant_kernel W r hrfg U, ← hk]
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    exact congrArg (fun k ↦ (k.app U).hom)
      (toSheafify_naturality J ((Functor.const W.ProEtᵒᵖ).map f)).symm

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem constant_projection (W : Scheme.{u}) (m : ℕ) (hm : 1 ≤ m) :
    integralConstantToCompletionOfUniverses l E W ≫
      (adicLisseForget W).map (PurCompactSupport.projection l E m hm W) =
      (adicLisseForget W).map
        ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk
            (Padic.coefficientExtensionIdeal l E m)).ulift.{u + 1, u + 1})) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  change integralConstantToCompletionOfUniverses l E W ≫
    (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (PurCompactSupport.projection l E (n + 1) hm W) =
        integralConstantQuotientOfUniverses l E W n
  have hp : PurCompactSupport.projection l E (n + 1) hm W =
      completedIntegralCommRingProjectionUnrestricted l E W n := by
    simp only [PurCompactSupport.projection, eqToHom_refl, Category.comp_id]
    congr 1
  rw [hp]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply RingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg (fun q ↦ (q.hom.app U).hom x)
    (limit.lift_π (integralConstantConeOfUniverses l E W) (op n))

private theorem lifted_quotient_kernel {A : Type u} [CommRing A] (I : Ideal A) :
    RingHom.ker (Ideal.Quotient.mk I).ulift.{u + 1, u + 1} =
      I.map (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A).toRingHom := by
  rw [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv]
  ext x
  change (Ideal.Quotient.mk I).ulift x = 0 ↔ x.down ∈ I
  exact ⟨fun h ↦ Ideal.Quotient.eq_zero_iff_mem.mp (congrArg ULift.down h),
    fun h ↦ ULift.ext (Ideal.Quotient.eq_zero_iff_mem.mpr h)⟩

private theorem lifted_coefficient_kernel_fg (m : ℕ) :
    (RingHom.ker (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l E m)).ulift.{u + 1, u + 1}).FG := by
  rw [lifted_quotient_kernel]
  apply Ideal.FG.map
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    ← Ideal.submodule_span_eq]
  exact Submodule.fg_span_singleton _

/-- The square of actual constant-to-finite coefficient maps is a pushout on sections.
This statement concerns only rings, without a module or a tensor comparison witness.

Source: Step 1 of `lem-pur-finite-quotient-module-balancing`; Stacks Project,
Modules on Sites, lemmas `lemma-constant-exact`, `lemma-tensor-with-finitely-presented`,
and `lemma-completion-flat` (Tag 093M); and the constant quotient cone of
`def-weil-completed-integral-coefficients`.
(blueprint: lem-pur-ramified-quotient-section-pushout).

Proof: put r=n+1, A=O_E and B=O_F. Taking rth powers of the ramification
identity gives map(A→B,(t^r))=(v^(er)). The limit-lift equation identifies
constant-to-completion followed by projection with the constant quotient map.
For a constant ring sheaf, the principal quotient map is surjective on sections:
a set-theoretic section of the discrete quotient gives a section after applying
the constant sheaf functor to sets and its comparison with underlying ring sheaves.
Its kernel on sections is the principal ideal of the constant section t^r.
Indeed the same constant-set construction applies to the surjection A→(t^r),
while preservation of finite limits identifies the latter constant set with the
kernel of the quotient map. The corresponding assertion holds for B and v^(er).
The image ideal in B(U) is therefore precisely the kernel of B(U)→B_n(U),
because the discrete ramification identity writes the two generators as multiples
of one another and these identities remain true on constant sections. Thus B_n(U)
is B(U) modulo the extension of the kernel of A(U)→A_n(U). The quotient universal
property gives the pushout, with lower map the specified ramified quotient lift;
commutativity is checked on discrete representatives, then sheafified. This also
works when U is empty (all section rings are zero), n=0, or e=1. No assertion that
evaluation preserves arbitrary sheaf colimits is used. -/
theorem ramifiedQuotient_sectionPushout (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :
    let g := integralConstantToCompletionOfUniverses l E W ≫
      (adicLisseForget W).map
        (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)
    let p := integralConstantToCompletionOfUniverses l F W ≫
      (adicLisseForget W).map
        (PurCompactSupport.projection l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W)
    ∀ U : W.ProEtᵒᵖ, IsPushout ((constantMap l E F i W).hom.app U)
      (CommRingCat.ofHom (show ((constants l E).ring W).obj.obj U →+*
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring W).obj.obj U
        from (g.hom.app U).hom))
      (CommRingCat.ofHom (show ((constants l F).ring W).obj.obj U →+*
        ((PurCompactSupport.finite l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring W).obj.obj U
        from (p.hom.app U).hom))
      (((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)).map W).hom.app U) := by
  dsimp only
  intro U
  have hE := congrArg (fun q ↦ (q.hom.app U).hom)
    (constant_projection l E W (n + 1) (Nat.le_add_left 1 n))
  have hF := congrArg (fun q ↦ (q.hom.app U).hom)
    (constant_projection l F W (e * (n + 1))
      (Nat.mul_pos hepos (Nat.le_add_left 1 n)))
  rw [hE, hF]
  change IsPushout
    (((constantSheaf (ProEt.topology W) CommRingCat).map
      (CommRingCat.ofHom (integralScalarIntegerInclusion l E F i).ulift)).hom.app U)
    (((constantSheaf (ProEt.topology W) CommRingCat).map
      (CommRingCat.ofHom (Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l E (n + 1))).ulift)).hom.app U)
    (((constantSheaf (ProEt.topology W) CommRingCat).map
      (CommRingCat.ofHom (Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l F (e * (n + 1)))).ulift)).hom.app U)
    (((constantSheaf (ProEt.topology W) CommRingCat).map
      (CommRingCat.ofHom (PurCompactSupport.ramifiedMap l E F i e he (n + 1)).ulift)
        ).hom.app U)
  apply constant_pushout
  · ext a
    rfl
  · intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.down
    exact ⟨ULift.up a, ULift.ext ha⟩
  · intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.down
    exact ⟨ULift.up a, ULift.ext ha⟩
  · simp only [CommRingCat.hom_ofHom]
    rw [lifted_quotient_kernel, lifted_quotient_kernel, Ideal.map_map]
    have he' := he
    change Ideal.map (integralScalarIntegerInclusion l E F i)
      (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1) =
        Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e at he'
    simp only [pow_one] at he'
    have hmap : Ideal.map (integralScalarIntegerInclusion l E F i)
        (Padic.coefficientExtensionIdeal l E (n + 1)) =
          Padic.coefficientExtensionIdeal l F (e * (n + 1)) := by
      simp only [Padic.coefficientExtensionIdeal, Ideal.map_pow, he', pow_mul]
    rw [← hmap, Ideal.map_map]
    rfl
  · exact lifted_coefficient_kernel_fg l E (n + 1)
  · exact lifted_coefficient_kernel_fg l F (e * (n + 1))

end WeilConjectures.PurStrictScalar
