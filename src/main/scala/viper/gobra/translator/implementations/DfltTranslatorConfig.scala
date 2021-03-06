// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.translator.implementations

import viper.gobra.translator.encodings.arrays.ArrayEncoding
import viper.gobra.translator.encodings.{BoolEncoding, IntEncoding, PointerEncoding, TypeEncoding}
import viper.gobra.translator.encodings.combinators.{FinalTypeEncoding, SafeTypeEncodingCombiner}
import viper.gobra.translator.encodings.sequences.SequenceEncoding
import viper.gobra.translator.encodings.sets.SetEncoding
import viper.gobra.translator.encodings.structs.StructEncoding
import viper.gobra.translator.implementations.components._
import viper.gobra.translator.implementations.translator._
import viper.gobra.translator.interfaces.TranslatorConfig
import viper.gobra.translator.interfaces.components._
import viper.gobra.translator.interfaces.translator._

class DfltTranslatorConfig(
  val field : Fields = new FieldsImpl,
  val array : Arrays = new ArraysImpl,
  val seqToSet : SeqToSet = new SeqToSetImpl,
  val seqMultiplicity : SeqMultiplicity = new SeqMultiplicityImpl,
  val fixpoint: Fixpoint = new FixpointImpl,
  val tuple : Tuples = new TuplesImpl,
  val equality: Equality = new EqualityImpl,
  val condition: Conditions = new ConditionsImpl,
  val unknownValue: UnknownValues = new UnknownValuesImpl,
  val typeEncoding: TypeEncoding = new FinalTypeEncoding(
    new SafeTypeEncodingCombiner(Vector(
      new BoolEncoding, new IntEncoding,
      new PointerEncoding, new StructEncoding, new ArrayEncoding,
      new SequenceEncoding, new SetEncoding
    ))
  ),
  val ass : Assertions = new AssertionsImpl,
  val expr : Expressions = new ExpressionsImpl,
  val method : Methods = new MethodsImpl,
  val pureMethod : PureMethods = new PureMethodsImpl,
  val predicate : Predicates = new PredicatesImpl,
  val stmt : Statements = new StatementsImpl
) extends TranslatorConfig {
  val seqToMultiset : SeqToMultiset = new SeqToMultisetImpl(seqMultiplicity)
}
