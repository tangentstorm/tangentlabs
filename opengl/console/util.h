#ifndef UTIL_H
#define UTIL_H

#include <string>
#include <vector>
#include <tuple>
#include "gl_core_3_3.h"

namespace util {
	/*
	* Read the entire contents of a file into a string, if an error occurs
	* the string will be empty
	*/
	std::string read_file(const std::string &fName);
	/*
	 * Load a GLSL shader from some file, returns -1 if loading failed
	 */
	GLint load_shader(GLenum type, const std::string &file);
	/*
	 * Build a shader program from the list of shaders passed
	 */
	GLint load_program(const std::vector<std::tuple<GLenum, std::string>> &shaders);
	/*
	 * Check for an OpenGL error and log it along with the message passed
	 * if an error occured. Will return true if an error occured & was logged
	 */
	bool log_glerror(const std::string &msg);
	/*
	 * A debug callback for the GL_ARB_debug_out extension
	 */
#ifdef _WIN32
	void APIENTRY gldebug_callback(GLenum src, GLenum type, GLuint id, GLenum severity,
		GLsizei len, const GLchar *msg, const GLvoid *user);
#else
	void gldebug_callback(GLenum src, GLenum type, GLuint id, GLenum severity,
		GLsizei len, const GLchar *msg, const GLvoid *user);
#endif
}

#endif
