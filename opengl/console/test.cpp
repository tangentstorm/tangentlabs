#include <iostream>
#include <iomanip>
#include <SDL.h>
#include "gl_core_3_3.h"
#include "util.h"

int main(int argc, char **argv){
	if (SDL_Init(SDL_INIT_EVERYTHING) != 0){
		std::cout << "SDL_Init error: " << SDL_GetError() << "\n";
		return 1;
	}
	SDL_GL_SetAttribute(SDL_GL_CONTEXT_MAJOR_VERSION, 3);
	SDL_GL_SetAttribute(SDL_GL_CONTEXT_MINOR_VERSION, 3);
	SDL_GL_SetAttribute(SDL_GL_CONTEXT_PROFILE_MASK, SDL_GL_CONTEXT_PROFILE_CORE);
	SDL_GL_SetAttribute(SDL_GL_CONTEXT_FLAGS, SDL_GL_CONTEXT_DEBUG_FLAG);

	SDL_Window *win = SDL_CreateWindow("Text Test", SDL_WINDOWPOS_CENTERED,
		SDL_WINDOWPOS_CENTERED, 640, 480, SDL_WINDOW_OPENGL);
	SDL_GLContext context = SDL_GL_CreateContext(win);

	if (ogl_LoadFunctions() == ogl_LOAD_FAILED){
		std::cout << "ogl load failed\n";
		SDL_GL_DeleteContext(context);
		SDL_DestroyWindow(win);
		SDL_Quit();
		return 1;
	}

	std::cout << "OpenGL Version: " << glGetString(GL_VERSION) << "\n"
		<< "OpenGL Vendor: " << glGetString(GL_VENDOR) << "\n"
		<< "OpenGL Renderer: " << glGetString(GL_RENDERER) << "\n"
		<< "GLSL Version: " << glGetString(GL_SHADING_LANGUAGE_VERSION) << "\n";

	glClearColor(0, 0, 0, 1);
	glClearDepth(1.f);
	glEnable(GL_DEPTH_TEST);
	glEnable(GL_DEBUG_OUTPUT_SYNCHRONOUS_ARB);
	glDebugMessageCallbackARB(util::gldebug_callback, NULL);
	glDebugMessageControlARB(GL_DONT_CARE, GL_DONT_CARE, GL_DONT_CARE, 0, NULL, GL_TRUE);

	GLint program = util::load_program({std::make_tuple(GL_VERTEX_SHADER, "../vertex.glsl"),
		std::make_tuple(GL_FRAGMENT_SHADER, "../fragment.glsl")});
	if (program == -1){
		SDL_GL_DeleteContext(context);
		SDL_DestroyWindow(win);
		SDL_Quit();
		return 1;
	}
	glUseProgram(program);

	const GLubyte img[] = {
		255, 0, 0, 255, 0, 255, 0, 255,
		0, 0, 255, 255, 255, 255, 0, 255
	};
	GLuint tex;
	glGenTextures(1, &tex);
	glBindTexture(GL_TEXTURE_2D, tex);
	glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, 2, 2, 0, GL_RGBA, GL_UNSIGNED_BYTE, img);
	//No mip-maps & use nearest-neighbor filtering
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAX_LEVEL, 0);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);

	GLuint vao, vbo;
	glGenVertexArrays(1, &vao);
	glBindVertexArray(vao);
	glGenBuffers(1, &vbo);
	glBindBuffer(GL_ARRAY_BUFFER, vbo);
	const int instances = 10;
	const int vars_per_instance = 3;
	//Instance data is: { x, y, uv_idx }
	GLint pos[instances * vars_per_instance] = {
		0, 0, 0,
		1, 0, 1,
		2, 0, 2,
		3, 0, 3,
		0, 1, 1,
		1, 1, 2,
		2, 1, 3,
		0, 2, 2,
		63, 15, 0,
		62, 15, 2
	};
	glBufferData(GL_ARRAY_BUFFER, vars_per_instance * instances * sizeof(GLint), pos, GL_STATIC_DRAW);
	glEnableVertexAttribArray(0);
	//Note: must use IPointer for integer types if you don't want them to be converted
	glVertexAttribIPointer(0, 2, GL_INT, vars_per_instance * sizeof(GLint), 0);
	glVertexAttribDivisor(0, 1);
	glEnableVertexAttribArray(1);
	glVertexAttribIPointer(1, 1, GL_INT, vars_per_instance * sizeof(GLint), (void*)(2 * sizeof(GLint)));
	glVertexAttribDivisor(1, 1);

	bool quit = false;
	while (!quit){
		SDL_Event e;
		while (SDL_PollEvent(&e)){
			if (e.type == SDL_QUIT || (e.type == SDL_KEYDOWN && e.key.keysym.sym == SDLK_ESCAPE)){
				quit = true;
				break;
			}
		}
		glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
		glDrawArraysInstanced(GL_TRIANGLE_STRIP, 0, 4, instances);
		SDL_GL_SwapWindow(win);
	}
	glDeleteProgram(program);
	glDeleteVertexArrays(1, &vao);
	SDL_GL_DeleteContext(context);
	SDL_DestroyWindow(win);
	SDL_Quit();
	return 0;
}
