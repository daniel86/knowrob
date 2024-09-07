/*
 * This file is part of KnowRob, please consult
 * https://github.com/knowrob/knowrob for license details.
 */

#include <boost/python.hpp>
#include <knowrob/knowrob.h>
#include <knowrob/Logger.h>
#include <knowrob/ThreadPool.h>
#include <filesystem>
#include <iostream>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include "knowrob/integration/python/PythonError.h"

uint32_t knowrob::GlobalSettings::batchSize_ = 500u;

knowrob::IRIAtomPtr knowrob::GlobalSettings::egoIRI_ =
		IRIAtom::Tabled("http://knowrob.org/kb/knowrob.owl#Self");

static bool initialized = false;

namespace knowrob {
	// stores the name of the executable as provided in argv[0]
	char *NAME_OF_EXECUTABLE = nullptr;

	char *getNameOfExecutable() {
		if (NAME_OF_EXECUTABLE) {
			return knowrob::NAME_OF_EXECUTABLE;
		} else {
			static char noExec[] = "<no-executable>";
			return noExec;
		}
	}

	void hashCombine(std::size_t &seed, const std::size_t &v) {
		static const auto GOLDEN_RATIO_HASH = static_cast<size_t>(0x9e3779b9);
		seed ^= v + GOLDEN_RATIO_HASH + (seed << 6) + (seed >> 2);
	}

	void insertUnique(std::ostream &os) {
		static boost::uuids::random_generator generator;
		std::hash<std::string> str_hash;
		os << std::setfill('0') << std::setw(8) << std::hex <<
		   str_hash(to_string(generator()));
	}

	void InitPythonPath() {
		std::stringstream pythonPath;
		auto oldPath = std::getenv("PYTHONPATH");
		if (oldPath) {
			pythonPath << oldPath << ":";
		}
		pythonPath <<
				   (std::filesystem::path(KNOWROB_INSTALL_PREFIX) / "knowrob").string() << ":"
				   << KNOWROB_SOURCE_DIR << ":"
				   << KNOWROB_BUILD_DIR;
		auto pythonPathStr = pythonPath.str();
		KB_DEBUG("[KnowRob] using python path: {}", pythonPathStr);
		setenv("PYTHONPATH", pythonPathStr.c_str(), 1);
	}

	void InitKnowRob(char **argv, bool initPython) {
		// remember the program name.
		// it is assumed here that argv stays valid during program execution.
		knowrob::NAME_OF_EXECUTABLE = argv[0];
		// set the locale to classic to avoid problems with number formatting,
		// especially regarding use of dot or comma as decimal separator.
		std::cout.imbue(std::locale::classic());
		// configure the logger
		Logger::initialize();
		// Allow Python to load modules KnowRob-related directories.
		InitPythonPath();
		if (initPython) {
			// Start a Python interpreter if it is not already initialized
			Py_Initialize();
			// Release the GIL which is acquired by Py_Initialize.
			// If we do not release it, then no other thread would be able
			// to run Python code.
			// So instead we always need to acquire the GIL in C++ code sections
			// that interact with Python (except of when the C++ code is launched
			// within Python in which case it actually already has the GIL).
			PyEval_SaveThread();
		}
		KB_INFO("[KnowRob] static initialization done.");
		KB_DEBUG("[KnowRob] source directory: {}", KNOWROB_SOURCE_DIR);
		KB_DEBUG("[KnowRob] install prefix: {}", KNOWROB_INSTALL_PREFIX);
		KB_DEBUG("[KnowRob] build directory: {}", KNOWROB_BUILD_DIR);
		initialized = true;
	}

	void InitKnowRob(int /*argc*/, char **argv, bool initPython) {
		InitKnowRob(argv, initPython);
	}

	static void InitKnowRobFromPython(boost::python::list py_argv) {
		if (initialized) return;

		static std::vector<std::string> arg_strings;
		static std::vector<char *> argv;

		for (auto i = 0; i < boost::python::len(py_argv); ++i) {
			std::string arg = boost::python::extract<std::string>(py_argv[i]);
			arg_strings.push_back(arg);
		}

		for (auto &str: arg_strings) {
			argv.push_back(str.data());
		}

		// Call the actual InitKnowRob function with the converted arguments
		knowrob::InitKnowRob(argv.data(), false);
	}

	void InitKnowRobFromPythonSysArgv() {
		if (initialized) return;

		using namespace boost::python;
		object sys = import("sys");
		list py_argv = extract<list>(sys.attr("argv"));
		// Add a default program name if sys.argv is empty or its first element is an empty string (seems to happen if
		// the python code is run without any arguments from the interpreter).
		if (len(py_argv) == 0 ||
			(len(py_argv) > 0 && extract<std::string>(py_argv[0]).check() &&
			 extract<std::string>(py_argv[0])().empty())) {
			py_argv[0] = "knowrob";
		}

		InitKnowRobFromPython(py_argv);
	}

	void ShutdownKnowRob() {
		// NOTE: Py_Finalize() should not be called when using boost python according to docs.
		//Py_Finalize();
		// stop the thread pool, join all remaining threads
		DefaultThreadPool()->shutdown();
		KB_INFO("[KnowRob] shutdown complete.");
	}
}

namespace knowrob::py {
	void staticKnowRobModuleInit() {
		using namespace boost::python;
		using namespace knowrob;

		/////////////////////////////////////////////////////
		// mappings for static functions
		def("InitKnowRobWithArgs", &InitKnowRobFromPython, "Initialize the Knowledge Base with arguments.");
		def("InitKnowRob", &InitKnowRobFromPythonSysArgv, "Initialize the Knowledge Base using sys.argv.");
		def("ShutdownKnowRob", &ShutdownKnowRob);
	}
}
