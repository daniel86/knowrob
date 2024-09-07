/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include "PythonTests.h"
#include <boost/python/extract.hpp>
#include "knowrob/URI.h"

namespace python = boost::python;
using namespace knowrob;

class JupyterTests : public PythonTests {
protected:
	// Per-test-suite set-up.
	static void SetUpTestSuite() {
		PythonTests::SetUpTestSuite("tests.py.test_jupyter");
	}
};

#define TEST_JUPYTER(notebook) EXPECT_NO_THROW(\
        PYTHON_TEST_CALL0("test_notebook", python::object(URI::resolve(notebook))));

TEST_F(JupyterTests, python_kb) { TEST_JUPYTER("jupyter/intro.ipynb"); }
