/*
  Copyright (C) 2011 Moritz Tenorth
  Copyright (C) 2018 Daniel Beßler
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:
      * Redistributions of source code must retain the above copyright
        notice, this list of conditions and the following disclaimer.
      * Redistributions in binary form must reproduce the above copyright
        notice, this list of conditions and the following disclaimer in the
        documentation and/or other materials provided with the distribution.
      * Neither the name of the <organization> nor the
        names of its contributors may be used to endorse or promote products
        derived from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
  ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
  (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/
:- module(action_effects,
    [
      action_effects_apply/1,
      action_effect_apply/2,
      action_effect_on_object/2,
      action_precondition_check/1,
      action_precondition_check/2,
      comp_actionEffectRule/2
    ]).
/** <module> Reasoning about action effects.

KnowRob mainly uses OWL as its knowledge representation language.
While being very expressive OWL still has some limitations.
First, action effects may establish new relations between objects.
We use SWRL to express this (knowrob_common:swrl.pl).
Second, actions may create/destroy objects. This can further not 
be expressed in SWRL.
Here, we use the computable mechanism of KnowRob and a set of Prolog 
rules that compute processStared, outputCreated, ... relations.
This has the nice side-effect that we can use computed relations
in SWRL rules (i.e., relate what was created to something else).

@author Moritz Tenorth
@author Daniel Beßler
@license BSD
*/

:- use_module(library('semweb/rdfs')).
:- use_module(library('semweb/rdf_db')).
:- use_module(library('semweb/owl')).
:- use_module(library('knowrob/swrl')).
:- use_module(library('knowrob/owl')).
:- use_module(library('knowrob/computable')).
:- use_module(library('knowrob/actions')).
:- use_module(library('knowrob/triple_memory')).

:- rdf_db:rdf_register_ns(knowrob, 'http://knowrob.org/kb/knowrob.owl#', [keep(true)]).
:- rdf_db:rdf_register_ns(ease, 'http://www.ease-crc.org/ont/EASE.owl#', [keep(true)]).
:- rdf_db:rdf_register_ns(swrl, 'http://www.w3.org/2003/11/swrl#', [keep(true)]).

:-  rdf_meta
    action_effects_apply(r),
    action_effect_apply(r,r),
    action_effect_on_object(r,t),
    action_precondition_check(r),
    action_precondition_check(r,r),
    comp_actionEffectRule(r,r),
    comp_processStarted(r,r),
    comp_outputsCreated(r,r),
    task_class_has_role(r,r,r).

%% comp_actionEffectRule(+Action:iri, ?Effect:iri)
%
% Effect is a RDF description of a SWRL rule that 
% describes how the effect of Action can be projected
% into the knowledge base.
%
% @param Action Instance of knowrob:Action
% @param Effect RDF name of SWRL rule
%
comp_actionEffectRule(Action, Effect) :-
  rdfs_individual_of(Action, ActionClass),
  rdf_has(Effect, knowrob:swrlActionConcept, literal(type(_,ActionClass))).

%% comp_actionEffectRule(+Action:iri, ?Process:iri)
comp_processStarted(Action,Process) :-
  %comp_action_participant(Action,knowrob:processStarted,Process).
  fail.
%% comp_outputsCreated(+Action:iri, ?Output:iri)
comp_outputsCreated(Action,Output) :-
  %comp_action_participant(Action,knowrob:outputsCreated,Output).
  fail.

%% action_effect_on_object(?Task:iri, ?EffectTerm:term) is nondet
%
% Reasoning about which Task
% has a desired effect on the object manipulated during the action.
% EffectTerm is a Prolog term describing the effect:
%
%	| updated(P,O)		   | If value O is specified for property P	  |
%	| created(Type)		   | If Type is a new type of the manipulated object	|
%	| destroyed(Type)	   | If Type is not a type of the manipulated object anymore after the action was performed	  |
%	| destroyed			   | If the object is not spatially existing anymore	  |
%
% `created` and `destroyed` effect terms follow the convention that type assertions
% are represented in rule heads as `Type(?obj)`, and type retractions as `(not Type)(?obj)`.
% 
% For example:
% ==
%     action_effect_on_object(knowrob:'TurningOnPoweredDevice',
%            updated(knowrob:stateOfObject,knowrob:'DeviceStateOn'))
%     action_effect_on_object(knowrob:'Cracking',
%            destroyed)
% ==
%
action_effect_on_object(Task, commited(Type)) :-
  task_class_has_role(Task,ease_obj:'CommitedObject',Type).
action_effect_on_object(Task, moved(Type)) :-
  task_class_has_role(Task,ease_obj:'MovedObject',Type).
action_effect_on_object(Task, operated(Type)) :-
  task_class_has_role(Task,ease_obj:'OperatedObject',Type).
action_effect_on_object(Task, removed(Type)) :-
  task_class_has_role(Task,ease_obj:'RemovedObject',Type).
action_effect_on_object(Task, transformed(Type)) :-
  task_class_has_role(Task,ease_obj:'TransformedObject',Type).
action_effect_on_object(Task, created(Type)) :-
  task_class_has_role(Task,ease_obj:'CreatedObject',Type).
action_effect_on_object(Task, destroyed(Type)) :-
  task_class_has_role(Task,ease_obj:'DestroyedObject',Type).

%%
task_class_has_role(Task,Role,ObjectType) :-
  owl_subclass_of(Task,Restr),
  rdf_has(Restr,owl:onProperty,dul:isTaskOf),
  owl_restriction_object_domain(Restr,RoleDescr),
  once((
    (\+ ground(Role) ; owl_subclass_of(RoleDescr,Role)),
    owl_property_range_on_class(RoleDescr,dul:classifies,ObjectType),
    rdfs_individual_of(ObjectType,owl:'Class')
  )).

%% action_effects_apply(+Act:iri)
%
% Apply all the effects that are known to apply if Act is performed successfully.
%
% @param Act Instance of knowrob:'Action'
%
action_effects_apply(Act) :-
  % make sure cached computables are inferred
  forall(rdfs_computable_has(Act, knowrob:processStarted, _), true),
  forall(rdfs_computable_has(Act, knowrob:outputsCreated, _), true),
  forall( comp_actionEffectRule(Act, Descr),
          action_effect_apply(Act, Descr) ).

%% action_effect_apply(+Act:iri,+Effect:iri)
%
% Effect is a RDF SWRL rule that expresses an effect of Act.
% The implications of the rule (i.e., the rule head) is
% projected to the RDF triple store with this call.
%
% SWRL action effect rules have additional annotations used to
% reason about the context in which the rule applies (i.e., the action class).
% These rules usually start with a statement `Action(?act)` which assigns an action instance
% to the rule. The action instance Act provided will be bound to this action variable in the rule.
%
% @param Act Instance of knowrob:'Action'
% @param Effect RDF description of SWRL action effect rule
%
action_effect_apply(Act,Effect) :-
  rdf(Act, knowrob:actionEffectProjected, Effect, action_projection), !.
action_effect_apply(Act,Effect) :-
  current_time(Now),
  % call projection rules
  rdf_has_prolog(Effect, knowrob:swrlActionVariable, Var),
  rdf_swrl_project(Effect, [var(Var,Act)]),
  % TODO: stop lifetime of inputs destroyed. i.e., making type a temporal property?
  % start/stop processes.
  forall(rdf_has(Act,knowrob:processStarted, Started),
         start_process(Started,Now)),
  forall(rdf_has(Act,knowrob:processStopped, Stopped),
         stop_process(Stopped,Now)),
  % remember that this effect was projected before to avoid
  % that it is projected again.
  rdf_assert(Act, knowrob:actionEffectProjected, Effect, action_projection),!.

start_process(Proc,Now) :-
  ( rdf_has(Proc, knowrob:startTime, _) ;
    rdf_assert_prolog(Proc, knowrob:startTime, Now) ),!.
start_process(Proc,Now) :-
  ( rdf_has(Proc, knowrob:endTime, _) ;
    rdf_assert_prolog(Proc, knowrob:endTime, Now) ),!.

%% action_precondition_check(+Act:iri).
%% action_precondition_check(+Act:iri,+Effect:iri).
%
% True if Act is an action without unsatisfied preconditions, or
% if Effect is a satisfied precondition of Act.
%
% @param Act Instance of knowrob:'Action'
% @param Effect RDF description of SWRL action effect rule
%
action_precondition_check(Act) :-
  action_precondition_check(Act, _), !.

action_precondition_check(Act, Effect) :-
  rdf_has_prolog(Effect, knowrob:swrlActionVariable, Var),
  rdf_swrl_satisfied(Effect, [var(Var,Act)]).

% % % % % % % % % % % % % % % % % % % % % % % % % % % % % % % %
% % % %  Utility predicates

swrl_type_of(_, O, O) :- !.
swrl_type_of(_, literal(type(_,X)), O) :- strip_literal_type(O,X),!.
swrl_type_of(_, O, literal(type(_,X))) :- strip_literal_type(O,X),!.
swrl_type_of(_Head :- Body, Var, Type) :-
  member(class(Type_rule, Var), Body),
  once(owl_subclass_of(Type, Type_rule)).
